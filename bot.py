#!/usr/bin/env python3
"""Бот «Стройка и недвижимость ДФО»: утренняя сводка новостей рынка (Приморье + крупное по ДФО)
и срочные уведомления о законах и нормах в сфере строительства.

Режимы:
    python bot.py --mode digest     # утренняя сводка: новости + законы за сутки
    python bot.py --mode alerts     # срочные уведомления: только новые законы и нормы
    python bot.py --mode digest --dry-run   # показать, ничего не отправлять и не сохранять

Переменные окружения: TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID (обязательно, кроме --dry-run),
MODE (digest|alerts — если не задан ключ --mode), HOURS (переопределить lookback_hours).
"""
from __future__ import annotations

import argparse
import datetime as dt
import html
import json
import logging
import os
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from email.utils import parsedate_to_datetime
from pathlib import Path
from urllib.parse import parse_qs, quote, urljoin, urlparse
from zoneinfo import ZoneInfo

import feedparser
import requests
import yaml

BASE_DIR = Path(__file__).resolve().parent
STATE_FILE = BASE_DIR / "state" / "state.json"
USER_AGENT = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/130.0 Safari/537.36")
TG_LIMIT = 3900
log = logging.getLogger("stroy")
UTC = dt.timezone.utc


# ================================================================ данные

@dataclass
class News:
    title: str
    url: str
    published: dt.datetime
    source: str
    domain: str
    snippet: str = ""
    region: str = ""                 # primorye | dfo | law
    group: str = ""                  # из какой группы запросов пришла
    also: list[str] = field(default_factory=list)   # другие издания с тем же сюжетом

    @property
    def key(self) -> str:
        return "n|" + re.sub(r"\W+", "", self.title.lower())[:90]


@dataclass
class Act:
    """Законодательное событие: проект акта, законопроект, закон, новость ведомства."""
    key: str
    title: str
    url: str
    source: str            # короткое имя источника
    level: str             # federal | regional
    kind: str = ""         # законопроект / закон / проект акта / новость
    date: str = ""         # дата из источника, если есть
    extra: str = ""        # стадия рассмотрения, разработчик и т.п.
    first_seen: str = ""


# ================================================================ утилиты

def now_utc() -> dt.datetime:
    return dt.datetime.now(UTC)


def esc(t: str) -> str:
    return html.escape(t or "", quote=False)


def href(u: str) -> str:
    return html.escape(u or "", quote=True)


def domain_of(url: str) -> str:
    host = (urlparse(url).hostname or "").lower()
    return host[4:] if host.startswith("www.") else host


def rx(words: list[str]) -> re.Pattern:
    return re.compile("|".join(f"(?:{w})" for w in words), re.IGNORECASE)


def http_get(url: str, timeout: int = 25) -> requests.Response:
    return requests.get(url, headers={"User-Agent": USER_AGENT, "Accept-Language": "ru,en;q=0.8"},
                        timeout=timeout)


def load_config(path: Path) -> dict:
    cfg = yaml.safe_load(path.read_text(encoding="utf-8"))
    cfg["_topic"] = rx(cfg["topic_words"])
    cfg["_prim"] = rx(cfg["primorye_words"])
    cfg["_dfo"] = rx(cfg["dfo_words"])
    cfg["_major"] = rx(cfg["dfo_major_words"])
    cfg["_law"] = rx(cfg["law_words"])
    cfg["_lawnews"] = rx(cfg["law_news_words"])
    cfg["_skip"] = rx(cfg["skip_words"]) if cfg.get("skip_words") else re.compile(r"(?!x)x")
    return cfg


def is_excluded(domain: str, cfg: dict) -> bool:
    return any(domain == d or domain.endswith("." + d) for d in cfg.get("exclude_domains", []))


def strip_html(t: str) -> str:
    return html.unescape(re.sub(r"<[^>]+>", " ", t or "")).replace("\xa0", " ").strip()


def words(t: str) -> set[str]:
    """Основы слов (первые 5 букв — грубо снимает падежи) и числа."""
    out = set()
    for w in re.findall(r"\w+", (t or "").lower().replace("ё", "е")):
        if w.isdigit():
            out.add(w)
        elif len(w) > 3:
            out.add(w[:5])
    return out


def similar(a: str, b: str, thr: float = 0.5) -> bool:
    wa, wb = words(a), words(b)
    return bool(wa and wb) and len(wa & wb) / len(wa | wb) >= thr


# ================================================================ состояние

def load_state() -> dict:
    try:
        st = json.loads(STATE_FILE.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        st = {}
    st.setdefault("seen", {})          # ключ -> когда впервые увидели
    st.setdefault("acts", [])          # журнал законодательных событий за неделю
    st.setdefault("bootstrapped", [])  # источники, по которым уже собран стартовый список
    return st


def save_state(st: dict) -> None:
    cutoff = now_utc() - dt.timedelta(days=45)
    st["seen"] = {k: v for k, v in st["seen"].items() if dt.datetime.fromisoformat(v) >= cutoff}
    week = now_utc() - dt.timedelta(days=7)
    st["acts"] = [a for a in st["acts"] if dt.datetime.fromisoformat(a["first_seen"]) >= week]
    STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
    STATE_FILE.write_text(json.dumps(st, ensure_ascii=False, indent=0), encoding="utf-8")


# ================================================================ законы и нормы

RU_MONTHS = {m: i for i, m in enumerate(
    ["january", "february", "march", "april", "may", "june", "july", "august", "september",
     "october", "november", "december"], 1)}


def parse_any_date(text: str) -> dt.datetime | None:
    m = re.search(r"(\d{1,2})\.(\d{1,2})\.(\d{4})", text or "")
    if m:
        return dt.datetime(int(m[3]), int(m[2]), int(m[1]), tzinfo=UTC)
    m = re.search(r"(\d{1,2}) ([A-Za-z]+) (\d{4})", text or "")
    if m and m[2].lower() in RU_MONTHS:
        return dt.datetime(int(m[3]), RU_MONTHS[m[2].lower()], int(m[1]), tzinfo=UTC)
    return None


def fetch_rss_acts(src: dict, cfg: dict) -> list[tuple[Act, dt.datetime | None, bool]]:
    """Возвращает (событие, дата публикации, проходит ли фильтр)."""
    r = http_get(src["url"])
    r.raise_for_status()
    feed = feedparser.parse(r.content)
    always = re.compile(src["always_if"], re.I) if src.get("always_if") else None
    out = []
    for e in feed.entries:
        title = strip_html(e.get("title", ""))
        desc = strip_html(e.get("summary", ""))
        author = e.get("author", "") or ""
        link = e.get("link", "") or src["url"]
        t = e.get("published_parsed") or e.get("updated_parsed")
        when = dt.datetime(*t[:6], tzinfo=UTC) if t else parse_any_date(desc)
        dev = re.search(r"Разработчик:\s*([^\n]+?)(?:\s+Процедура:|\s+Вид:|$)", desc)
        kind_m = re.search(r"Вид:\s*([^\n]+?)$", desc)
        passes = (bool(cfg["_law"].search(title)) or bool(always and always.search(author + " " + desc))) \
            and not cfg["_skip"].search(title)
        act = Act(key=f"{src['short']}|{link}", title=title, url=link, source=src["short"],
                  level=src["level"], kind=(kind_m[1].strip() if kind_m else "проект акта")
                  if "regulation" in src["url"] else "новость",
                  date=when.strftime("%d.%m.%Y") if when else "",
                  extra=("разработчик: " + dev[1].strip()) if dev else "")
        out.append((act, when, passes))
    return out


def fetch_link_acts(src: dict, cfg: dict) -> list[tuple[Act, dt.datetime | None, bool]]:
    from bs4 import BeautifulSoup
    r = http_get(src["url"])
    r.raise_for_status()
    soup = BeautifulSoup(r.text, "html.parser")
    pat = re.compile(src["link_pattern"])
    found: dict[str, str] = {}
    for a in soup.find_all("a", href=True):
        path = a["href"].split("?")[0]
        if path.startswith("http"):
            path = urlparse(path).path
        text = re.sub(r"\s+", " ", a.get_text(" ")).strip()
        if pat.match(path) and len(text) > 15 and not re.fullmatch(r"(Читать далее|Подробнее)\.*", text, re.I):
            url = urljoin(src["base"], path)
            if len(text) > len(found.get(url, "")):
                found[url] = text
    out = []
    for url, title in found.items():
        act = Act(key=f"{src['short']}|{url}", title=title, url=url, source=src["short"],
                  level=src["level"], kind="новость")
        out.append((act, None, bool(cfg["_law"].search(title)) and not cfg["_skip"].search(title)))
    return out


ZSPK_RE = re.compile(
    r"№\s*(?P<num>[^\s]+)\s+Дата внесения:\s*(?P<date>\d{2}\.\d{2}\.\d{4})\s+(?P<title>.+?)\s+"
    r"Инициатор:\s*(?P<init>.+?)\s+Ответственный комитет:\s*(?P<com>.+?)"
    r"(?:\s+Стадия рассмотрения:\s*(?P<stage>.+?))?"
    r"(?=\s+Файлы:|\s+\d{1,3}\s+№|\s+©|\s*$)", re.S)


def fetch_zspk_acts(src: dict, cfg: dict) -> list[tuple[Act, dt.datetime | None, bool]]:
    from bs4 import BeautifulSoup
    r = http_get(src["url"])
    r.raise_for_status()
    soup = BeautifulSoup(r.text, "html.parser")
    links = []
    for a in soup.find_all("a", href=True):
        if "/Doc/" in a["href"]:
            links.append((re.sub(r"\s+", " ", a.get_text(" ")).strip(), urljoin(src["base"], a["href"])))
    text = re.sub(r"\s+", " ", soup.get_text(" "))
    out = []
    for m in ZSPK_RE.finditer(text):
        title = m["title"].strip()
        url = next((u for t, u in links if t and title.startswith(t[:40])), src["url"])
        stage = (m["stage"] or "").strip()
        # стадия входит в ключ: переход законопроекта на новую стадию — тоже новость
        key = f"zspk|{m['num']}|{stage}"
        when = parse_any_date(m["date"])
        act = Act(key=key, title=title, url=url, source=src["short"], level="regional",
                  kind=src.get("kind", ""), date=m["date"],
                  extra=f"№ {m['num']}" + (f" · стадия: {stage}" if stage else ""))
        out.append((act, when, bool(cfg["_law"].search(title)) and not cfg["_skip"].search(title)))
    return out


FETCHERS = {"rss": fetch_rss_acts, "links": fetch_link_acts, "zspk": fetch_zspk_acts}


def collect_acts(cfg: dict, st: dict, hours: int) -> tuple[list[Act], list[str]]:
    """Опрашивает источники законов. Возвращает новые события (прошедшие фильтр) и список
    источников, которые не открылись. При первом опросе источника только запоминает,
    что на нём уже есть, чтобы не прислать сразу весь архив."""
    new_acts, failed = [], []
    cutoff = now_utc() - dt.timedelta(hours=hours)

    def run(src):
        try:
            return src, FETCHERS[src["type"]](src, cfg), None
        except Exception as exc:
            return src, [], exc

    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(run, cfg.get("legal_sources", [])))

    for src, items, err in results:
        if err is not None:
            log.warning("Источник не открылся: %s (%s)", src["name"], err)
            failed.append(src["name"])
            continue
        if not items:   # на этих страницах всегда что-то есть: пусто = сайт поменял вёрстку или отдал заглушку
            log.warning("Источник открылся, но записей не нашлось: %s", src["name"])
            failed.append(src["name"] + " (пусто)")
            continue
        first_time = src["name"] not in st["bootstrapped"]
        for act, when, passes in items:
            if act.key in st["seen"]:
                continue
            st["seen"][act.key] = now_utc().isoformat()
            if not passes:
                continue
            # при первом опросе берём только то, что точно свежее (есть дата в пределах окна)
            if first_time and not (when and when >= cutoff):
                continue
            act.first_seen = now_utc().isoformat()
            new_acts.append(act)
        if first_time:
            st["bootstrapped"].append(src["name"])
            log.info("Источник «%s»: стартовый список запомнен (%d записей)", src["name"], len(items))
    st["acts"].extend(a.__dict__ for a in new_acts)
    return new_acts, failed


# ================================================================ новости

def google_url(q: str, hours: int) -> str:
    when = "1d" if hours <= 24 else "2d"
    return (f"https://news.google.com/rss/search?q={quote(q + ' when:' + when)}"
            f"&hl=ru&gl=RU&ceid=RU%3Aru")


def bing_url(q: str, hours: int) -> str:
    interval = "7" if hours <= 24 else "8"
    return (f"https://www.bing.com/news/search?q={quote(q)}&format=rss"
            f"&qft=interval%3d%22{interval}%22&setlang=ru&cc=ru")


def parse_feed_news(content: bytes, kind: str) -> list[News]:
    feed = feedparser.parse(content)
    out = []
    for e in feed.entries:
        t = e.get("published_parsed") or e.get("updated_parsed")
        if not t:
            continue
        published = dt.datetime(*t[:6], tzinfo=UTC)
        title = strip_html(e.get("title", ""))
        link = e.get("link", "")
        if kind == "google":
            src = e.get("source") or {}
            name, src_url = src.get("title", ""), src.get("href", "")
            if name and title.endswith(" - " + name):
                title = title[: -len(name) - 3]
            dom = domain_of(src_url)
            snippet = ""
        else:
            qs = parse_qs(urlparse(link).query)
            if "url" in qs:
                link = qs["url"][0]
            dom = domain_of(link)
            name = e.get("news_source", "") or dom
            snippet = strip_html(e.get("summary", ""))
        if dom:
            out.append(News(title=title.strip(), url=link, published=published, source=name or dom,
                            domain=dom, snippet=snippet))
    return out


def collect_news(cfg: dict, hours: int) -> tuple[list[News], int]:
    queries = [(g, q) for g in ("primorye", "dfo", "federal_law") for q in cfg["news_queries"].get(g, [])]
    jobs = [("google", g, google_url(q, hours)) for g, q in queries] + \
           [("bing", g, bing_url(q, hours)) for g, q in queries]

    def run(job):
        kind, group, url = job
        try:
            r = http_get(url)
            r.raise_for_status()
            items = parse_feed_news(r.content, kind)
            for n in items:
                n.group = group
            return items, True
        except Exception as exc:
            log.info("Лента не открылась: %s", exc)
            return [], False

    with ThreadPoolExecutor(max_workers=6) as pool:
        res = list(pool.map(run, jobs))
    cutoff = now_utc() - dt.timedelta(hours=hours)
    items = [n for batch, _ in res for n in batch if n.published >= cutoff]
    failed = sum(1 for _, ok in res if not ok)
    return items, failed


def resolve_google(items: list[News]) -> None:
    todo = [n for n in items if "news.google.com" in n.url]
    if not todo:
        return
    try:
        from googlenewsdecoder import gnewsdecoder
    except ImportError:
        return
    for n in todo:
        try:
            res = gnewsdecoder(n.url, interval=1)
            if res.get("success"):
                n.url = res["decoded_url"]
        except Exception:
            pass


def article_text(url: str) -> str:
    try:
        import trafilatura
        r = http_get(url, timeout=20)
        if r.status_code >= 400:
            return ""
        return trafilatura.extract(r.text, url=url, include_comments=False, favor_recall=True) or ""
    except Exception:
        return ""


def first_relevant_sentence(text: str, cfg: dict, limit: int) -> str:
    for s in re.split(r"(?<=[.!?])\s+|\n+", text or ""):
        s = re.sub(r"\s+", " ", s).strip()
        if len(s) > 40 and cfg["_topic"].search(s):
            return s if len(s) <= limit else s[:limit].rsplit(" ", 1)[0] + "…"
    return ""


def select_news(raw: list[News], cfg: dict, st: dict) -> list[News]:
    # 1) дубли и уже присланное
    uniq: dict[str, News] = {}
    for n in sorted(raw, key=lambda x: (x.domain == "", -x.published.timestamp())):
        if is_excluded(n.domain, cfg) or n.key in st["seen"]:
            continue
        uniq.setdefault(n.key, n)
    cands = list(uniq.values())
    resolve_google(cands)

    # 2) текст статьи: для фильтра и выдержки
    def enrich(n: News) -> News:
        text = article_text(n.url)
        n._text = text  # type: ignore[attr-defined]
        if not n.snippet:
            n.snippet = first_relevant_sentence(text, cfg, cfg.get("max_snippet_chars", 220))
        else:
            n.snippet = n.snippet[: cfg.get("max_snippet_chars", 220)]
        return n

    with ThreadPoolExecutor(max_workers=8) as pool:
        cands = list(pool.map(enrich, cands))

    # 3) тема и география; федеральные законы — отдельно
    kept = []
    for n in cands:
        if n.group == "federal_law":
            if cfg["_law"].search(n.title) and cfg["_lawnews"].search(n.title):
                n.region = "law"
                kept.append(n)
            continue
        blob = f"{n.title} {n.snippet} {getattr(n, '_text', '')[:3000]}"
        if not cfg["_topic"].search(f"{n.title} {n.snippet}") and not cfg["_topic"].search(blob[:1500]):
            continue
        head = f"{n.title} {n.snippet}"
        if cfg["_prim"].search(head) or cfg["_prim"].search(blob[:1500]):
            n.region = "primorye"
        elif cfg["_dfo"].search(blob) and cfg["_major"].search(blob):
            n.region = "dfo"
        else:
            continue
        kept.append(n)

    # 4) один сюжет — один пункт, остальные издания перечисляем
    clusters: list[News] = []
    for n in sorted(kept, key=lambda x: -x.published.timestamp()):
        twin = next((c for c in clusters if similar(c.title, n.title)), None)
        if twin:
            if n.source not in twin.also and n.source != twin.source:
                twin.also.append(n.source)
        else:
            clusters.append(n)

    prim = [n for n in clusters if n.region == "primorye"][: cfg.get("max_primorye", 20)]
    dfo = [n for n in clusters if n.region == "dfo"][: cfg.get("max_dfo", 8)]
    law = [n for n in clusters if n.region == "law"][: cfg.get("max_law_news", 6)]
    return prim + dfo + law


# ================================================================ сообщения

def chunk(blocks: list[str]) -> list[str]:
    msgs, cur = [], ""
    for b in blocks:
        if len(b) > TG_LIMIT:
            b = b[: TG_LIMIT - 20] + "…"
        cand = f"{cur}\n\n{b}" if cur else b
        if len(cand) > TG_LIMIT:
            msgs.append(cur)
            cur = b
        else:
            cur = cand
    if cur:
        msgs.append(cur)
    return msgs


def render_news(n: News, tz: ZoneInfo) -> str:
    when = n.published.astimezone(tz).strftime("%d.%m %H:%M")
    lines = [f"▪️ <b>{esc(n.source)}</b> · {when}", f'<a href="{href(n.url)}">{esc(n.title)}</a>']
    if n.snippet and not similar(n.snippet, n.title, 0.8):
        lines.append(f"<i>{esc(n.snippet)}</i>")
    if n.also:
        lines.append("Также: " + esc(", ".join(n.also[:5])))
    return "\n".join(lines)


ICONS = {"законопроект": "📝", "закон": "✅", "новость": "📰"}


def render_act(a: Act) -> str:
    icon = ICONS.get(a.kind, "📄")
    head = f"{icon} <b>{esc(a.source)}</b>" + (f" · {esc(a.kind)}" if a.kind and a.kind != "новость" else "")
    if a.date:
        head += f" · {esc(a.date)}"
    lines = [head, f'<a href="{href(a.url)}">{esc(a.title)}</a>']
    if a.extra:
        lines.append(f"<i>{esc(a.extra)}</i>")
    return "\n".join(lines)


def build_digest(news: list[News], acts: list[Act], cfg: dict, failed_news: int,
                 failed_sources: list[str], alerted_keys: set[str]) -> list[str]:
    tz = ZoneInfo(cfg.get("timezone", "UTC"))
    today = dt.datetime.now(tz).strftime("%d.%m.%Y")
    prim = [n for n in news if n.region == "primorye"]
    dfo = [n for n in news if n.region == "dfo"]
    law_news = [n for n in news if n.region == "law"]
    fed = [a for a in acts if a.level == "federal"]
    reg = [a for a in acts if a.level == "regional"]
    blocks = [f"<b>🏗 Стройка и недвижимость · {today}</b>\n"
              f"Приморье: {len(prim)} · ДФО: {len(dfo)} · законы и нормы: {len(acts) + len(law_news)}"]
    if prim:
        blocks.append("<b>━━ Приморье ━━</b>")
        blocks += [render_news(n, tz) for n in prim]
    if dfo:
        blocks.append("<b>━━ Крупное по ДФО ━━</b>")
        blocks += [render_news(n, tz) for n in dfo]
    if reg or fed or law_news:
        blocks.append("<b>━━ Законы и нормы ━━</b>")
        for title, group in (("Приморье", reg), ("Федеральные: документы", fed)):
            if group:
                blocks.append(f"<b>{title}</b>")
                blocks += [render_act(a) + ("\n<i>⚡ уже присылали срочно</i>" if a.key in alerted_keys else "")
                           for a in group]
        if law_news:
            blocks.append("<b>Федеральные: в СМИ</b>")
            blocks += [render_news(n, tz) for n in law_news]
    if not (news or acts):
        blocks.append("За сутки новых материалов не нашлось.")
    foot = "<i>Новости: Google News, Bing News"
    if failed_news:
        foot += f" (не открылось лент: {failed_news})"
    if failed_sources:
        foot += " · не открылись источники законов: " + esc(", ".join(failed_sources))
    blocks.append(foot + "</i>")
    return chunk(blocks)


def build_alert(acts: list[Act]) -> list[str]:
    blocks = [f"<b>⚡ Законы и нормы: новое ({len(acts)})</b>"]
    reg = [a for a in acts if a.level == "regional"]
    fed = [a for a in acts if a.level == "federal"]
    if reg:
        blocks.append("<b>Приморье</b>")
        blocks += [render_act(a) for a in reg]
    if fed:
        blocks.append("<b>Федеральные</b>")
        blocks += [render_act(a) for a in fed]
    return chunk(blocks)


def send_telegram(messages: list[str]) -> None:
    token, chat = os.environ["TELEGRAM_BOT_TOKEN"], os.environ["TELEGRAM_CHAT_ID"]
    for text in messages:
        r = requests.post(f"https://api.telegram.org/bot{token}/sendMessage",
                          json={"chat_id": chat, "text": text, "parse_mode": "HTML",
                                "disable_web_page_preview": True}, timeout=30)
        if not r.ok:
            raise RuntimeError(f"Telegram ответил {r.status_code}: {r.text[:300]}")
        time.sleep(1.1)


# ================================================================ запуск

def main() -> int:
    ap = argparse.ArgumentParser(description="Стройка и недвижимость ДФО")
    ap.add_argument("--mode", choices=["digest", "alerts"], default=os.environ.get("MODE") or "digest")
    ap.add_argument("--hours", type=int, default=int(os.environ.get("HOURS") or 0) or None)
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--config", default=str(BASE_DIR / "config.yaml"))
    args = ap.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")

    cfg = load_config(Path(args.config))
    hours = args.hours or cfg.get("lookback_hours", 30)
    if not args.dry_run and not (os.environ.get("TELEGRAM_BOT_TOKEN") and os.environ.get("TELEGRAM_CHAT_ID")):
        log.error("Не заданы TELEGRAM_BOT_TOKEN и TELEGRAM_CHAT_ID")
        return 2

    st = load_state()
    new_acts, failed_sources = collect_acts(cfg, st, hours)
    log.info("Законы и нормы: новых %d, не открылось источников %d", len(new_acts), len(failed_sources))

    if args.mode == "alerts":
        if new_acts:
            msgs = build_alert(new_acts)
            if args.dry_run:
                print("\n\n──────────\n\n".join(msgs))
            else:
                send_telegram(msgs)
                st.setdefault("alerted", [])
                st["alerted"] = (st["alerted"] + [a.key for a in new_acts])[-500:]
        if not args.dry_run:
            save_state(st)
        return 0

    # digest: законы за окно (в т.ч. уже присланные срочно) + новости
    cutoff = now_utc() - dt.timedelta(hours=hours)
    acts = [Act(**a) for a in st["acts"] if dt.datetime.fromisoformat(a["first_seen"]) >= cutoff]
    raw, failed_news = collect_news(cfg, hours)
    news = select_news(raw, cfg, st)
    log.info("Новостей после отбора: %d", len(news))
    if not (news or acts) and not cfg.get("send_empty", True):
        return 0
    msgs = build_digest(news, acts, cfg, failed_news, failed_sources, set(st.get("alerted", [])))
    if args.dry_run:
        print("\n\n──────────\n\n".join(msgs))
        return 0
    send_telegram(msgs)
    for n in news:
        st["seen"][n.key] = now_utc().isoformat()
    save_state(st)
    return 0


if __name__ == "__main__":
    sys.exit(main())
