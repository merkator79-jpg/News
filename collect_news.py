#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
collect_news.py: сбор новостей из лент sources.yaml и построение страницы news.html.

Каждый запуск:
  1. забирает новости из всех лент (адреса и правила берет из sources.yaml и denylist.txt);
  2. выбрасывает ссылки на запрещенные сайты и на сайты не из источника;
  3. сохраняет в базу news.db только заголовок, ссылку, время и категорию (текст статей не копируется);
  4. склеивает заметки об одном и том же событии из разных изданий в один сюжет;
  5. строит страницу news.html с рейтингом и фильтрами и отчет collect_report.txt.

Нужен Python 3.8+ и модуль PyYAML.
"""

import argparse
import hashlib
import html
import json
import re
import sqlite3
import sys
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit

try:
    import yaml
except ImportError:
    sys.exit("Не найден модуль PyYAML. Выполните в командной строке: pip install pyyaml")

try:
    sys.stdout.reconfigure(errors="replace")
except Exception:
    pass

USER_AGENT = "Mozilla/5.0 (compatible; PersonalNewsAggregator/1.0)"
TIMEOUT_SECONDS = 20
KEEP_DAYS = 400              # столько дней хранить заметки в базе
PAGE_DAYS = 370             # столько дней показывать на странице (нужно для фильтра "год")
FULL_DAYS = 31              # последние дни показываем все сюжеты, более старые - только заметные
MAX_OLD_CLUSTERS = 4000     # сколько старых (заметных) сюжетов оставлять на странице
CLUSTER_DAYS = 4            # заметки за эти дни склеиваются заново при каждом запуске
CLUSTER_GAP_HOURS = 96      # заметки дальше друг от друга по времени не склеиваются
MAX_CLUSTERS_ON_PAGE = 8000
HN_TOP_COUNT = 60           # сколько верхних историй Hacker News учитывать

# Вес издания в рейтинге: насколько "засчитывается" его заметка при подсчете охвата сюжета.
SOURCE_WEIGHT = {
    "dumskaya": 0.8, "ain": 0.8, "dou": 0.8, "itc": 0.8,
    "dw": 0.5, "aljazeera": 0.5, "mit-news-ai": 0.5,
    "hacker-news": 0.0,   # HN дает только отдельный бонус по очкам, не охват
}
IT_SOURCES = {"ain", "dou", "itc", "hacker-news"}
AI_SOURCES = {"mit-news-ai"}

TRACKING_PARAMS = {"fbclid", "gclid", "traffic_source", "ref", "ref_src", "source", "cmpid", "ocid"}


# ---------- адреса и запрещенные сайты ----------

def idna(text):
    try:
        return text.encode("idna").decode("ascii")
    except UnicodeError:
        return text


def load_denylist(path):
    rules = []
    for line in Path(path).read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip().lower()
        if not line:
            continue
        rules.append("." + idna(line[1:]) if line.startswith(".") else idna(line))
    return rules


def denied_by(host, rules):
    if not host:
        return None
    host = idna(host.lower().rstrip("."))
    for rule in rules:
        if rule.startswith("."):
            if host.endswith(rule):
                return rule
        elif host == rule or host.endswith("." + rule):
            return rule
    return None


def host_matches(host, domains):
    host = (host or "").lower()
    return any(host == d or host.endswith("." + d) for d in domains)


def normalize_url(url):
    """Приводит ссылку к единому виду, чтобы одна и та же статья не попала дважды."""
    parts = urlsplit(url.strip())
    host = (parts.hostname or "").lower()
    if host.startswith("www."):
        host = host[4:]
    query = [(k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True)
             if not k.lower().startswith("utm_") and k.lower() not in TRACKING_PARAMS]
    path = parts.path.rstrip("/") or "/"
    port = f":{parts.port}" if parts.port and parts.port not in (80, 443) else ""
    return urlunsplit(("https", host + port, path, urlencode(query), ""))


# ---------- сеть и разбор лент ----------

def fetch(url, timeout=TIMEOUT_SECONDS):
    req = urllib.request.Request(url, headers={
        "User-Agent": USER_AGENT,
        "Accept": "application/rss+xml, application/xml, text/xml, application/json, */*",
    })
    with urllib.request.urlopen(req, timeout=timeout) as response:
        return response.read()


def describe_error(error):
    if isinstance(error, urllib.error.HTTPError):
        return f"сайт ответил ошибкой {error.code}"
    if isinstance(error, urllib.error.URLError):
        return f"не удалось подключиться ({error.reason})"
    if isinstance(error, TimeoutError):
        return f"сайт не ответил за {TIMEOUT_SECONDS} секунд"
    if isinstance(error, ET.ParseError):
        return f"это не читаемый RSS ({error})"
    return f"{type(error).__name__}: {error}"


def parse_date(text):
    if not text:
        return None
    text = text.strip()
    parsed = None
    try:
        parsed = parsedate_to_datetime(text)
    except (TypeError, ValueError):
        parsed = None
    if parsed is None:
        try:
            parsed = datetime.fromisoformat(text.replace("Z", "+00:00"))
        except ValueError:
            return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return int(parsed.timestamp())


def local_name(tag):
    return tag.rsplit("}", 1)[-1] if isinstance(tag, str) else ""


def clean_text(text):
    text = html.unescape(text or "")
    text = re.sub(r"<[^>]+>", " ", text)
    return re.sub(r"\s+", " ", text).strip()


def parse_feed(data):
    root = ET.fromstring(data)
    items = []
    for element in root.iter():
        if local_name(element.tag) not in ("item", "entry"):
            continue
        item = {"title": "", "link": "", "date": None, "cats": []}
        for child in element:
            name = local_name(child.tag)
            if name == "title":
                item["title"] = clean_text(child.text)
            elif name == "link":
                href = child.get("href")
                if href:
                    if not item["link"] or child.get("rel") in (None, "alternate"):
                        item["link"] = href.strip()
                elif child.text and not item["link"]:
                    item["link"] = child.text.strip()
            elif name in ("pubDate", "published", "updated", "date") and item["date"] is None:
                item["date"] = parse_date(child.text)
            elif name == "category":
                value = clean_text(child.text or child.get("term"))
                if value:
                    item["cats"].append(value)
        items.append(item)
    return items


# ---------- категория и география ----------

def rx(pattern):
    return re.compile(pattern, re.IGNORECASE)


AI_RE = rx(r"штучн\w*\s+інтелект|искусственн\w*\s+интеллект|\bші\b|\bии\b|нейромереж|нейросет|openai|chatgpt|\bgpt|anthropic|\bclaude\b|gemini|\bllm|\bai\b|artificial intelligence|machine learning|deepseek|copilot|midjourney|генеративн|language model|мовна модель|языков\w+ модел")
SPORT_RE = rx(r"футбол|баскетбол|волейбол|теніс|тенис|олімп|олимп|чемпіонат|чемпионат|чемпіон|кубок|матч|збірн|сборн|\bліга\b|\bлига\b|uefa|fifa|\bнба\b|\bnba\b|\bnhl\b|\bufc\b|бокс|гімнаст|легкоатлет|біатлон|формул\w+\s*1|formula 1|wimbledon|трансфер|голкіпер|football|soccer|tennis|cricket|rugby|olympic|premier league|champions league|\bsport")
IT_RE = rx(r"смартфон|iphone|android|\bios\b|windows|macos|linux|процесор|процессор|відеокарт|видеокарт|nvidia|\bamd\b|\bintel\b|apple|google|microsoft|samsung|xiaomi|стартап|startup|кібер|кибер|cyber|хакер|hacker|вразливіст|уязвимост|vulnerab|програміст|программист|розробник|разработчик|developer|software|програмн|программн|гаджет|ноутбук|\bps5\b|xbox|steam|квантов|\bчіп(?:и|ів|ах|ом|ами)?\b|\bчип(?:ы|ов|ах|ом|ами)?\b|semiconductor|blockchain|криптовалют|bitcoin|біткоїн|github|python|javascript|\bchip|\bapp\b|\bcloud\b|хмарн\w*\s+(?:сервіс|обчисл|технолог|сховищ|інфраструктур|платформ)")
POL_RE = rx(r"зеленськ|зеленск|zelensk|путін|путин|putin|трамп|trump|верховн\w+\s+рад|парламент|parliament|президент|president|уряд|правительств|government|кабмін|міністр|министр|minister|депутат|вибор|выбор|election|санкц|sanction|перемовин|переговор|negotiat|\bнато\b|\bnato\b|євросоюз|евросоюз|\bєс\b|\beu\b|європарламент|законопроєкт|законопроект|партія|партия|\bparty\b|прем'єр|премьер|prime minister|мерія|мэрия|\bмер\b")
ODESA_RE = rx(r"одес|одещ|odes")
UKRAINE_RE = rx(r"україн|украин|ukrain|київ|киев|kyiv|kiev|зеленськ|зеленск|zelensk|харків|харьков|kharkiv|дніпр|днепр|запоріж|запорож|zaporiz|херсон|kherson|львів|львов|lviv")


def classify(source_id, source_country, url, title, cats):
    text = f"{title} {' '.join(cats)}"
    path = url.lower()

    # категория
    if source_id in AI_SOURCES:
        category = "ai"
    elif AI_RE.search(text):
        category = "ai"
    elif source_id in IT_SOURCES:
        category = "it"
    elif "rubric-sports" in path or "/sport" in path or re.search(r"спорт", " ".join(cats), re.I) or SPORT_RE.search(text):
        category = "sport"
    elif IT_RE.search(text):
        category = "it"
    elif "rubric-polytics" in path or re.search(r"політик|политик", " ".join(cats), re.I) or POL_RE.search(text):
        category = "politics"
    else:
        category = "other"

    # география
    if source_id == "dumskaya" or ODESA_RE.search(text) or "/odesa" in path or "odessa" in path:
        geo = "odesa"
    elif source_country == "UA":
        geo = "world" if ("rubric-world" in path or "/world" in path or "/svit" in path) else "ukraine"
    else:
        geo = "ukraine" if UKRAINE_RE.search(text) else "world"
    return category, geo


# ---------- сбор ----------

def collect_feed(source, deny_rules, timeout):
    res = {"id": source["id"], "name": source.get("name") or source["id"], "items": [], "total": 0,
           "dropped": Counter(), "error": None}
    domains = [source["domain"].lower()] + [d.lower() for d in source.get("extra_domains", [])]
    try:
        feed_items = parse_feed(fetch(source["feed_url"], timeout))
    except Exception as error:
        res["error"] = describe_error(error)
        return res
    res["total"] = len(feed_items)
    for item in feed_items:
        link, title = item["link"], item["title"]
        if not link or not title or not link.lower().startswith(("http://", "https://")):
            res["dropped"]["без ссылки или заголовка"] += 1
            continue
        host = urlsplit(link).hostname
        if denied_by(host, deny_rules):
            res["dropped"]["запрещенный сайт"] += 1
            continue
        if not host_matches(host, domains):
            res["dropped"]["ссылка не на сайт источника"] += 1
            continue
        low = link.lower()
        if "/video/" in low or "/gallery/" in low:
            res["dropped"]["видео или галерея"] += 1
            continue
        res["items"].append({
            "url": normalize_url(link), "title": title, "published": item["date"],
            "cats": item["cats"], "hn_score": 0, "hn_comments": 0,
        })
    return res


def collect_hn(source, deny_rules, timeout):
    res = {"id": source["id"], "name": source.get("name") or source["id"], "items": [], "total": 0,
           "dropped": Counter(), "error": None}
    try:
        ids = json.loads(fetch(source["api_url"], timeout))[:HN_TOP_COUNT]
    except Exception as error:
        res["error"] = describe_error(error)
        return res
    base = source["api_url"].rsplit("/", 1)[0]

    def one(story_id):
        try:
            return json.loads(fetch(f"{base}/item/{story_id}.json", timeout)) or {}
        except Exception:
            return {}

    with ThreadPoolExecutor(max_workers=8) as pool:
        stories = list(pool.map(one, ids))
    res["total"] = len(stories)
    for story in stories:
        url = story.get("url") or ""
        if story.get("type") != "story" or story.get("dead") or story.get("deleted") or not url.lower().startswith(("http://", "https://")):
            res["dropped"]["без внешней ссылки"] += 1
            continue
        if denied_by(urlsplit(url).hostname, deny_rules):
            res["dropped"]["запрещенный сайт"] += 1
            continue
        res["items"].append({
            "url": normalize_url(url), "title": clean_text(story.get("title")),
            "published": int(story["time"]) if story.get("time") else None, "cats": [],
            "hn_score": int(story.get("score", 0)), "hn_comments": int(story.get("descendants", 0)),
        })
    return res


# ---------- база ----------

def open_db(path):
    con = sqlite3.connect(path)
    con.execute("""CREATE TABLE IF NOT EXISTS items(
        url TEXT PRIMARY KEY, source TEXT, title TEXT, published INTEGER, first_seen INTEGER,
        cats TEXT, category TEXT, geo TEXT, hn_score INTEGER DEFAULT 0, hn_comments INTEGER DEFAULT 0,
        cluster TEXT)""")
    con.execute("CREATE INDEX IF NOT EXISTS ix_items_pub ON items(published)")
    return con


def store(con, source, country, items, now):
    new = 0
    for item in items:
        published = item["published"] or now
        published = min(published, now)
        category, geo = classify(source["id"], country, item["url"], item["title"], item["cats"])
        row = (item["url"], source["id"], item["title"], published, now, " | ".join(item["cats"]),
               category, geo, item["hn_score"], item["hn_comments"])
        if source["id"] == "hacker-news":
            # очки HN дописываются к уже известной статье, в том числе чужой
            cur = con.execute("UPDATE items SET hn_score=?, hn_comments=? WHERE url=?",
                              (item["hn_score"], item["hn_comments"], item["url"]))
            if cur.rowcount == 0:
                con.execute("INSERT INTO items(url,source,title,published,first_seen,cats,category,geo,hn_score,hn_comments) VALUES (?,?,?,?,?,?,?,?,?,?)", row)
                new += 1
        else:
            existing = con.execute("SELECT source FROM items WHERE url=?", (item["url"],)).fetchone()
            if existing is None:
                con.execute("INSERT INTO items(url,source,title,published,first_seen,cats,category,geo,hn_score,hn_comments) VALUES (?,?,?,?,?,?,?,?,?,?)", row)
                new += 1
            elif existing[0] == "hacker-news":
                # статья пришла сначала через HN: теперь записываем ее за настоящим изданием
                con.execute("UPDATE items SET source=?, title=?, published=?, cats=?, category=?, geo=? WHERE url=?",
                            (source["id"], item["title"], published, row[5], category, geo, item["url"]))
    return new


def reclassify(con, sources, now):
    """Пересчитывает категории и регион у заметок на странице: правила могли измениться после обновления программы."""
    country = {s["id"]: s.get("country", "") for s in sources}
    rows = con.execute("SELECT url, source, title, cats, category, geo FROM items WHERE published >= ?",
                       (now - FULL_DAYS * 86400,)).fetchall()
    changed = 0
    for url, src, title, cats, cat, geo in rows:
        cat_list = [c for c in (cats or "").split(" | ") if c]
        new_cat, new_geo = classify(src, country.get(src, ""), url, title, cat_list)
        if (new_cat, new_geo) != (cat, geo):
            con.execute("UPDATE items SET category=?, geo=? WHERE url=?", (new_cat, new_geo, url))
            changed += 1
    return changed


# ---------- склейка одинаковых сюжетов ----------

STOP = set("""что как это для при про над під від після через якщо але або також щоб його її їх вже ще
який яка які якої якому якою тому саме після перед вона воно вони стало буде була були мають може можуть
как так для при что это его она они был была были будет после перед также или уже еще который которая
the and for with that this from have has had was were are will would after over into about amid says said
new news more than their they them but not you your out who its has been""".split())


def stems(title):
    words = re.findall(r"[0-9a-zа-яіїєґё']+", title.lower().replace("ё", "е"))
    out = set()
    for word in words:
        if word in STOP:
            continue
        if word.isdigit():
            if len(word) >= 2:
                out.add(word)
        elif len(word) >= 4:
            out.add(word[:5])
    return out


def recluster(con, now):
    since = now - CLUSTER_DAYS * 86400
    rows = con.execute("SELECT url, title, published FROM items WHERE published >= ?", (since,)).fetchall()
    n = len(rows)
    tokens = [stems(r[1]) for r in rows]
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    index = defaultdict(list)
    for i, toks in enumerate(tokens):
        for t in toks:
            index[t].append(i)
    gap = CLUSTER_GAP_HOURS * 3600
    for i in range(n):
        counts = Counter()
        for t in tokens[i]:
            posting = index[t]
            if len(posting) > 300:        # слишком частое слово, не помогает искать пары
                continue
            for j in posting:
                if j < i:
                    counts[j] += 1
        for j, shared in counts.items():
            if abs(rows[i][2] - rows[j][2]) > gap:
                continue
            union = len(tokens[i] | tokens[j])
            if shared >= 5 or (shared >= 3 and shared / union >= 0.4):
                ri, rj = find(i), find(j)
                if ri != rj:
                    parent[ri] = rj
    groups = defaultdict(list)
    for i in range(n):
        groups[find(i)].append(i)
    for members in groups.values():
        first = min(members, key=lambda k: (rows[k][2], rows[k][0]))
        cluster_id = "c" + hashlib.sha1(rows[first][0].encode("utf-8")).hexdigest()[:10]
        for k in members:
            con.execute("UPDATE items SET cluster=? WHERE url=?", (cluster_id, rows[k][0]))
    return len(groups)


# ---------- страница ----------

def short_name(name):
    name = re.sub(r"\s*\(.*?\)", "", name)
    return name.split(":", 1)[0].strip()


def build_page(con, sources, now, out_path):
    since = now - PAGE_DAYS * 86400
    rows = con.execute("""SELECT url, source, title, published, category, geo, hn_score, hn_comments, cluster
                          FROM items WHERE published >= ?""", (since,)).fetchall()
    groups = defaultdict(list)
    for r in rows:
        key = r[8] or ("c" + hashlib.sha1(r[0].encode("utf-8")).hexdigest()[:10])
        groups[key].append(r)

    clusters = []
    for key, members in groups.items():
        members.sort(key=lambda r: r[3])
        best = max(members, key=lambda r: (SOURCE_WEIGHT.get(r[1], 1.0), -r[3]))
        geo = Counter(r[5] for r in members).most_common(1)[0][0]
        cat = Counter(r[4] for r in members).most_common(1)[0][0]
        items = sorted(members, key=lambda r: -SOURCE_WEIGHT.get(r[1], 1.0))[:15]
        clusters.append({
            "t": best[2], "u": best[0], "g": geo, "c": cat,
            "i": [[r[1], r[3], r[0], r[6], r[7]] for r in items],
            "n": max(r[3] for r in members),
        })
    # свежие сюжеты берем все; старые (для недели/месяца/года) - только заметные, чтобы страница не разрасталась
    edge = now - FULL_DAYS * 86400
    recent = [c for c in clusters if c["n"] >= edge]
    old = []
    for c in clusters:
        if c["n"] >= edge:
            continue
        distinct = len({x[0] for x in c["i"]})
        hn = max((x[3] or 0) for x in c["i"])
        if distinct >= 2 or hn >= 100:
            c["i"] = c["i"][:6]
            old.append((distinct + min(hn / 300, 1.5), c))
    old.sort(key=lambda t: -t[0])
    old = [c for _, c in old[:MAX_OLD_CLUSTERS]]
    recent.sort(key=lambda c: -c["n"])
    clusters = recent[:MAX_CLUSTERS_ON_PAGE] + old
    clusters.sort(key=lambda c: -c["n"])

    src = {}
    for s in sources:
        src[s["id"]] = [short_name(s.get("name") or s["id"]), SOURCE_WEIGHT.get(s["id"], 1.0)]
    data = {"gen": now, "since": min((r[3] for r in rows), default=now), "src": src, "cl": clusters}
    payload = json.dumps(data, ensure_ascii=False, separators=(",", ":"))
    payload = payload.replace("<", "\\u003c").replace("\u2028", "\\u2028").replace("\u2029", "\\u2029")
    Path(out_path).write_text(PAGE.replace("__DATA__", payload), encoding="utf-8")
    return len(clusters), len(rows)


PAGE = r'''<!doctype html>
<html lang="uk">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Новини</title>
<script>
(function () {
  var t = "";
  try { t = localStorage.getItem("news-theme") || ""; } catch (e) {}
  if (t !== "dark" && t !== "light" && t !== "cappuccino") {
    t = (window.matchMedia && matchMedia("(prefers-color-scheme: dark)").matches) ? "dark" : "light";
  }
  document.documentElement.setAttribute("data-theme", t);
})();
</script>
<style>
:root{
  --bg:#edf1f3;--card:#fff;--ink:#10242f;--mute:#5e7380;--line:#d3dde3;--chip:#e3eaee;
  --sea:#1b6b93;--amber:#e8a020;--onsea:#fff;--odesa:#b57712;--hn:#b3590a;--rain:#7cc4ee;
  --harbor:#0e2433;--hink:#e7eef2;--hmute:#8fa8b6;--hline:rgba(255,255,255,.14);--hcard:rgba(255,255,255,.07);
  --c-politics:#2f7db5;--c-sport:#2e9e6b;--c-it:#7b61e0;--c-ai:#c23b8f;--c-other:#7c8e99;
  --head:Bahnschrift,"Segoe UI Variable Display","Segoe UI",system-ui,sans-serif;
  --body:"Segoe UI Variable Text","Segoe UI",system-ui,-apple-system,Roboto,sans-serif;
}
:root[data-theme=dark]{
  --bg:#0a141c;--card:#101f2b;--ink:#e6eef2;--mute:#8ca3b0;--line:#1e3341;--chip:#162a38;
  --sea:#5bb3de;--amber:#f2b440;--onsea:#07202d;--odesa:#f2b440;--hn:#f0a05a;--rain:#7cc4ee;
  --harbor:#07101a;--hline:rgba(255,255,255,.1);
  --c-politics:#5aa6dc;--c-sport:#47c28b;--c-it:#9c88f2;--c-ai:#e46bb4;--c-other:#8a9ca7;
}
:root[data-theme=cappuccino]{
  --bg:#eadccb;--card:#faf3e8;--ink:#3a2a20;--mute:#7b6453;--line:#d8c4ac;--chip:#e6d5bf;
  --sea:#8a5535;--amber:#c88524;--onsea:#fff8ee;--odesa:#a4630f;--hn:#a2501a;--rain:#e2b98c;
  --harbor:#3b271c;--hink:#f6e8d7;--hmute:#c6a98d;--hline:rgba(255,235,210,.18);--hcard:rgba(255,235,210,.09);
  --c-politics:#4d7898;--c-sport:#5a8a48;--c-it:#7a58a6;--c-ai:#b5446d;--c-other:#8c7767;
}
:root[data-theme=cappuccino] .seg button[aria-pressed=true]{box-shadow:0 1px 3px rgba(60,35,15,.25)}
*{box-sizing:border-box}
html,body{margin:0;height:100%;overflow:hidden}
body{background:var(--bg);color:var(--ink);font:15px/1.45 var(--body)}
button{font:inherit;color:inherit}
:focus-visible{outline:2px solid var(--sea);outline-offset:2px}
.app{height:100vh;display:flex;flex-direction:column}

/* ---- шапка-табло ---- */
.top{flex:none;display:flex;align-items:center;gap:28px;padding:10px 16px;min-height:108px;background:var(--harbor);color:var(--hink)}
.brand{width:234px;flex:none}
.brand h1{display:flex;align-items:center;gap:10px;margin:0 0 4px;font:600 28px/1 var(--head);letter-spacing:.01em}
.lamp{width:11px;height:11px;border-radius:50%;background:var(--amber);box-shadow:0 0 0 3px rgba(232,160,32,.25),0 0 14px rgba(232,160,32,.7)}
.lamp.busy{animation:pulse .9s ease-in-out infinite}
@keyframes pulse{50%{opacity:.35;box-shadow:0 0 0 6px rgba(232,160,32,.08)}}
.upd{color:var(--hmute);font-size:12.5px;line-height:1.45;white-space:pre-line}
.clock{flex:none;width:250px;text-align:center;font-variant-numeric:tabular-nums;font-family:var(--head)}
.clock .time{font-size:50px;font-weight:300;line-height:1;letter-spacing:.02em}
.clock .sec{font-size:20px;color:var(--amber);margin-left:4px}
.clock .date{margin-top:6px;color:var(--hmute);font:400 13px var(--body)}
.wx{flex:1;min-width:0;display:flex;align-items:center;gap:12px}
.wx-now{flex:none;display:flex;align-items:center;gap:12px;padding:8px 16px 8px 12px;background:var(--hcard);border:1px solid var(--hline);border-radius:10px}
.wx-ico{font-size:38px;line-height:1}
.wx-t{font:300 34px/1 var(--head);font-variant-numeric:tabular-nums}
.wx-d{font-size:12px;color:var(--hmute);line-height:1.4}
.wx-d b{color:var(--hink);font-weight:600}
.wx-days{flex:1;min-width:0;display:flex;gap:6px;overflow:hidden}
.day{flex:1 1 0;min-width:62px;text-align:center;padding:6px 4px;border:1px solid var(--hline);border-radius:8px;background:var(--hcard);font-size:12px;line-height:1.3;font-variant-numeric:tabular-nums}
.day .dn{color:var(--hmute);font-size:11.5px}
.day .di{font-size:22px;line-height:1.25}
.day .dt{font-weight:600}
.day .dt span{color:var(--hmute);font-weight:400}
.day .dp{color:var(--rain);font-size:11px}
.wx-msg{color:var(--hmute);font-size:13px}

.themes{flex:none;display:flex;gap:6px;align-self:flex-start}
.themes button{width:30px;height:30px;padding:0;border-radius:50%;border:2px solid var(--hline);cursor:pointer;transition:transform .15s,border-color .15s}
.themes button:hover{transform:scale(1.1)}
.themes button[aria-pressed=true]{border-color:var(--amber);box-shadow:0 0 0 2px rgba(255,255,255,.12)}
.themes button[data-t=dark]{background:linear-gradient(135deg,#0a141c 50%,#5bb3de 50%)}
.themes button[data-t=light]{background:linear-gradient(135deg,#edf1f3 50%,#1b6b93 50%)}
.themes button[data-t=cappuccino]{background:linear-gradient(135deg,#eadccb 50%,#8a5535 50%)}

/* ---- каркас ---- */
.fbtn{display:none}
.layout{flex:1;min-height:0;display:grid;grid-template-columns:262px minmax(0,1fr);gap:24px;padding:0 16px}
.side{overflow-y:auto;padding:16px 6px 18px 0}
.side::-webkit-scrollbar,main::-webkit-scrollbar{width:7px}
.side::-webkit-scrollbar-thumb,main::-webkit-scrollbar-thumb{background:var(--line);border-radius:4px}
main{overflow-y:auto;padding:14px 8px 20px 0;min-width:0}
.grp{margin:0 0 20px}
.grp>h2{margin:0 0 7px;font:600 13px/1.2 var(--head);color:var(--mute);letter-spacing:.02em}
.note{margin:7px 0 0;font-size:12px;line-height:1.4;color:var(--mute)}

/* ---- сегменты: сортировка, период, интервал ---- */
.seg{display:grid;grid-auto-flow:column;grid-auto-columns:1fr;gap:2px;padding:3px;background:var(--chip);border-radius:9px}
.seg button{border:0;background:transparent;white-space:nowrap;padding:6px 2px;border-radius:6px;cursor:pointer;font-size:12.5px;line-height:1.2;color:var(--mute);transition:background .15s,color .15s}
.seg button small{display:block;margin-top:2px;font-size:11px;font-variant-numeric:tabular-nums;opacity:.8}
.seg button:hover{color:var(--ink)}
.seg button[aria-pressed=true]{background:var(--card);color:var(--ink);font-weight:600;box-shadow:0 1px 3px rgba(5,25,40,.18)}

/* ---- меню: регион, категория ---- */
.menu button{display:flex;align-items:center;gap:9px;width:100%;padding:6px 10px;border:0;border-left:3px solid transparent;border-radius:0 6px 6px 0;background:transparent;text-align:left;cursor:pointer;transition:background .15s}
.menu button:hover{background:var(--chip)}
.menu button[aria-pressed=true]{background:var(--chip);border-left-color:var(--sea);font-weight:600}
.menu .dot{width:8px;height:8px;border-radius:50%;background:var(--c-other);flex:none}
.menu .n{margin-left:auto;color:var(--mute);font-size:12.5px;font-weight:400;font-variant-numeric:tabular-nums}
.menu button.odesa .dot{background:var(--amber)}
.menu button[data-v=politics] .dot{background:var(--c-politics)}
.menu button[data-v=sport] .dot{background:var(--c-sport)}
.menu button[data-v=it] .dot{background:var(--c-it)}
.menu button[data-v=ai] .dot{background:var(--c-ai)}
.menu button[data-v=all] .dot{background:transparent;border:1.5px solid var(--mute)}

input.q{width:100%;padding:9px 11px;border:1px solid var(--line);border-radius:7px;background:var(--card);color:var(--ink);font:inherit;font-size:14px}
input.q::placeholder{color:var(--mute)}

/* ---- управление обновлением ---- */
.ctl{margin:0 0 22px;padding:12px;background:var(--card);border:1px solid var(--line);border-radius:10px}
.ctl[hidden]{display:none}
.ctl-off{margin:0 0 22px;padding:10px 12px;border:1px dashed var(--line);border-radius:10px;font-size:12.5px;line-height:1.4;color:var(--mute)}
.ctl-off[hidden]{display:none}
.ctl-off a{color:var(--sea)}
.ctl h2{margin:0 0 7px;font:600 13px/1.2 var(--head);color:var(--mute)}
button.go{display:block;width:100%;margin-top:10px;padding:9px 12px;border:0;border-radius:7px;background:var(--sea);color:var(--onsea);font-weight:600;font-size:14px;cursor:pointer;transition:filter .15s}
button.go:hover{filter:brightness(1.08)}
button.go:disabled{opacity:.6;cursor:default}
.ctl .st{display:block;margin:8px 0 0;color:var(--mute);font-size:12.5px;line-height:1.4}
button.off{margin:8px 0 0;padding:0;border:0;background:none;color:var(--mute);font-size:12px;text-decoration:underline;cursor:pointer}
button.off:hover{color:var(--ink)}

/* ---- сюжеты ---- */
.item{position:relative;display:flex;gap:14px;margin:0 0 10px;padding:13px 16px 13px 20px;background:var(--card);border:1px solid var(--line);border-radius:6px;transition:border-color .15s}
.item:hover{border-color:var(--sea)}
.beam{position:absolute;left:0;top:0;bottom:0;width:5px;border-radius:6px 0 0 6px;background:var(--amber);transform-origin:top}
.intro .beam{animation:grow .7s ease-out both}
@keyframes grow{from{transform:scaleY(0)}}
.num{flex:none;min-width:30px;text-align:right;padding-top:1px;font:300 26px/1.05 var(--head);color:var(--mute);font-variant-numeric:tabular-nums}
.num.hot{color:var(--amber);font-weight:600}
.body{min-width:0;flex:1}
a.t{color:var(--ink);text-decoration:none;font:600 18px/1.3 var(--head);letter-spacing:.005em;overflow-wrap:anywhere}
a.t:hover{color:var(--sea)}
a.t:visited{color:var(--mute)}
.meta{display:flex;flex-wrap:wrap;align-items:center;gap:6px 14px;margin-top:8px;font-size:12.5px;color:var(--mute)}
.geo{font-weight:600;color:var(--mute)}
.geo.odesa{color:var(--odesa)}
.cat{display:inline-flex;align-items:center;gap:6px}
.cat i{width:8px;height:8px;border-radius:50%;background:var(--c-other)}
.cat[data-c=politics] i{background:var(--c-politics)}
.cat[data-c=sport] i{background:var(--c-sport)}
.cat[data-c=it] i{background:var(--c-it)}
.cat[data-c=ai] i{background:var(--c-ai)}
.cov{color:var(--ink);font-weight:600}
.hn{color:var(--hn);font-weight:600}
.srcs{display:flex;flex-wrap:wrap;gap:5px}
a.chip{padding:1px 8px;border-radius:4px;background:var(--chip);color:var(--ink);text-decoration:none;font-size:12px}
a.chip:hover{background:var(--sea);color:var(--onsea)}
.more{display:block;margin:16px auto 4px;padding:9px 26px;border:1px solid var(--line);border-radius:7px;background:var(--card);cursor:pointer}
.more:hover{border-color:var(--sea)}
.more[hidden]{display:none}
.empty{padding:48px 0;text-align:center;color:var(--mute)}
.empty button{margin-top:12px;padding:8px 18px;border:1px solid var(--line);border-radius:7px;background:var(--card);cursor:pointer}
@media (prefers-reduced-motion:reduce){.lamp.busy,.intro .beam{animation:none}*{transition:none!important}}
@media (max-width:900px){
  html,body{height:auto;overflow:auto}.app{height:auto}
  .top{flex-wrap:wrap;gap:12px}.brand{width:auto}
  .layout{display:block;padding:0 12px}
  .fbtn{display:block;width:100%;margin:12px 0 4px;padding:11px;border:1px solid var(--line);border-radius:8px;background:var(--card);cursor:pointer;font-weight:600}
  .side{display:none}.side.open{display:block}
  .clock{width:auto}.top{padding:10px 12px}.clock .time{font-size:40px}.side,main{overflow:visible;padding-right:0}
  .wx{flex-basis:100%}.wx-days{overflow-x:auto}
}
</style>
</head>
<body>
<div class="app">
<header class="top">
 <div class="brand"><h1><span class="lamp" id="lamp"></span>Новини</h1><div class="upd" id="upd"></div></div>
 <div class="clock notranslate" translate="no"><div><span class="time" id="clk-t"></span><span class="sec" id="clk-s"></span></div><div class="date" id="clk-d"></div></div>
 <div class="wx notranslate" translate="no" id="wx"><span class="wx-msg">Погода в Одесі завантажується…</span></div>
 <div class="themes notranslate" translate="no" id="themes" role="group" aria-label="Тема">
  <button data-t="dark" title="Темна" aria-label="Темна тема"></button>
  <button data-t="light" title="Світла" aria-label="Світла тема"></button>
  <button data-t="cappuccino" title="Капучіно" aria-label="Тема капучіно"></button>
 </div>
</header>
<div class="layout">
<button class="fbtn" id="fbtn" aria-expanded="false">Фільтри та налаштування ▾</button>
<aside class="side" id="side">
 <div class="ctl-off" id="ctl-off" hidden>Автооновлення та кнопка «Оновити зараз» доступні, коли сторінку відкрито програмою. Запустіть її ярликом «Новини» на робочому столі або відкрийте <a href="http://127.0.0.1:8787/">127.0.0.1:8787</a>.</div>
 <div class="ctl" id="ctl" hidden>
  <h2>Автооновлення</h2>
  <div class="seg" id="g-int"></div>
  <button class="go" id="now">Оновити зараз</button>
  <span class="st" id="st"></span>
  <button class="off" id="quit" title="Зупинити програму">Вимкнути програму</button>
 </div>
 <div class="grp notranslate" translate="no"><h2>Тема</h2><div class="seg" id="g-theme"><button data-t="dark">Темна</button><button data-t="light">Світла</button><button data-t="cappuccino">Капучіно</button></div></div>
 <div class="grp"><h2>Сортування</h2><div class="seg" id="g-sort"></div></div>
 <div class="grp"><h2>Період</h2><div class="seg" id="g-period"></div><p class="note" id="hist" hidden></p></div>
 <div class="grp"><h2>Регіон</h2><div class="menu" id="g-geo"></div></div>
 <div class="grp"><h2>Категорія</h2><div class="menu" id="g-cat"></div></div>
 <div class="grp"><input class="q" id="q" type="search" placeholder="Пошук у заголовках" aria-label="Пошук у заголовках"></div>
</aside>
<main id="main">
<div id="list" class="intro"></div>
<button class="more" id="more" hidden>Показати ще</button>
</main>
</div>
</div>
<script>
const D = __DATA__;
const OPT = {
  sort:[["rating","За рейтингом"],["fresh","За актуальністю"]],
  period:[["day","День"],["week","Тиждень"],["month","Місяць"],["year","Рік"]],
  geo:[["all","Усі"],["odesa","Одеса"],["ukraine","Україна"],["world","Світ"]],
  cat:[["all","Усі"],["politics","Політика"],["sport","Спорт"],["it","IT"],["ai","ШІ"],["other","Інше"]]
};
const WIN = {day:86400, week:7*86400, month:31*86400, year:365*86400};
const GEO_NAME = {odesa:"Одеса", ukraine:"Україна", world:"Світ"};
const CAT_NAME = {politics:"Політика", sport:"Спорт", it:"IT", ai:"ШІ", other:"Інше"};
const PAGE = 50;
let S = {sort:"rating", period:"day", geo:"all", cat:"all", q:"", shown:PAGE};

try {
  const h = new URLSearchParams(location.hash.slice(1));
  for (const k of ["sort","period","geo","cat"]) {
    const v = h.get(k);
    if (v && OPT[k].some(o => o[0] === v)) S[k] = v;
  }
  S.q = h.get("q") || "";
} catch (e) {}

function setTheme(t, store) {
  document.documentElement.setAttribute("data-theme", t);
  if (store) { try { localStorage.setItem("news-theme", t); } catch (e) {} }
  document.querySelectorAll("#themes button, #g-theme button").forEach(b => b.setAttribute("aria-pressed", b.dataset.t === t ? "true" : "false"));
}
document.querySelectorAll("#themes button, #g-theme button").forEach(b => { b.onclick = () => setTheme(b.dataset.t, true); });
setTheme(document.documentElement.getAttribute("data-theme"), false);

document.getElementById("fbtn").onclick = () => {
  const o = document.getElementById("side").classList.toggle("open");
  document.getElementById("fbtn").setAttribute("aria-expanded", o ? "true" : "false");
};

function save() {
  try {
    const h = new URLSearchParams();
    for (const k of ["sort","period","geo","cat"]) h.set(k, S[k]);
    if (S.q) h.set("q", S.q);
    history.replaceState(null, "", "#" + h.toString());
  } catch (e) {}
}

function el(tag, cls, text) {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text !== undefined) e.textContent = text;
  return e;
}
const toTop = () => { document.getElementById("main").scrollTop = 0; };

// ---- фильтры: считаем, сколько сюжетов дадет каждый пункт ----
function passGeo(c, geo) {
  if (geo === "all") return true;
  if (geo === "odesa") return c.g === "odesa";
  if (geo === "ukraine") return c.g === "ukraine" || c.g === "odesa";
  return c.g === "world";
}
function passCat(c, cat) { return cat === "all" || c.c === cat; }
function inWindow(c, period, now) { return c.i.some(x => Math.min(x[1], now) >= now - WIN[period]); }
function passQ(c) { const q = S.q.trim().toLowerCase(); return !q || c.t.toLowerCase().includes(q); }

function counts() {
  const now = Date.now() / 1000;
  const r = {period:{day:0, week:0, month:0, year:0}, geo:{all:0, odesa:0, ukraine:0, world:0}, cat:{all:0, politics:0, sport:0, it:0, ai:0, other:0}};
  for (const c of D.cl) {
    if (!passQ(c)) continue;
    const g = passGeo(c, S.geo), k = passCat(c, S.cat);
    if (g && k) for (const p in WIN) if (inWindow(c, p, now)) r.period[p]++;
    if (!inWindow(c, S.period, now)) continue;
    if (k) for (const v in r.geo) if (passGeo(c, v)) r.geo[v]++;
    if (g) for (const v in r.cat) if (passCat(c, v)) r.cat[v]++;
  }
  return r;
}

function buildGroups() {
  const n = counts();
  for (const key of ["sort", "period", "geo", "cat"]) {
    const box = document.getElementById("g-" + key);
    box.textContent = "";
    for (const [val, label] of OPT[key]) {
      const b = el("button");
      b.dataset.k = key; b.dataset.v = val;
      b.setAttribute("aria-pressed", S[key] === val ? "true" : "false");
      if (key === "sort") b.textContent = label;
      else if (key === "period") { b.appendChild(document.createTextNode(label)); b.appendChild(el("small", "", String(n.period[val]))); }
      else {
        b.appendChild(el("span", "dot")); b.appendChild(document.createTextNode(label));
        b.appendChild(el("span", "n", String(n[key][val])));
        if (key === "geo" && val === "odesa") b.classList.add("odesa");
      }
      b.onclick = () => { S[key] = val; S.shown = PAGE; save(); render(); toTop(); };
      box.appendChild(b);
    }
  }
  // сколько истории в базе
  const hist = document.getElementById("hist");
  const span = Date.now() / 1000 - D.since;
  if (D.since && span < WIN[S.period] * 0.92) {
    const h = span / 3600;
    const txt = h < 48 ? Math.max(1, Math.round(h)) + " год" : (h / 24).toFixed(1).replace(".", ",") + " доби";
    hist.textContent = "У базі новини за останні " + txt + ". Цей період наповнюватиметься з часом.";
    hist.hidden = false;
  } else hist.hidden = true;
}

function ago(sec) {
  const m = Math.max(0, Math.round(sec / 60));
  if (m < 2) return "щойно";
  if (m < 60) return m + " хв тому";
  const h = Math.round(m / 60);
  if (h < 24) return h + " год тому";
  const d = Math.round(h / 24);
  return d + " дн тому";
}
function sources(n) {
  const a = n % 10, b = n % 100;
  return n + (a === 1 && b !== 11 ? " джерело" : (a >= 2 && a <= 4 && (b < 12 || b > 14) ? " джерела" : " джерел"));
}

function compute() {
  const now = Date.now() / 1000;
  const win = WIN[S.period], half = win / 3;
  const fw = S.period === "day" ? 0.5 : 0.2;   // у довгих періодах важить охоплення, а не свіжість
  const out = [];
  for (const c of D.cl) {
    if (!passGeo(c, S.geo) || !passCat(c, S.cat) || !passQ(c)) continue;
    const inWin = c.i.filter(x => Math.min(x[1], now) >= now - win);
    if (!inWin.length) continue;
    const seen = {}; let cover = 0, hn = 0, hnc = 0, newest = 0;
    for (const x of inWin) {
      const w = (D.src[x[0]] || ["", 1])[1];
      if (!(x[0] in seen)) { seen[x[0]] = 1; cover += w; }
      if (x[3] > hn) { hn = x[3]; hnc = x[4]; }
      newest = Math.max(newest, Math.min(x[1], now));
    }
    const bonus = Math.min(hn / 300, 1.5);
    const age = now - newest;
    const fresh = Math.pow(0.5, age / half);
    out.push({c, srcs:Object.keys(seen), newest, hn, hnc, score:(cover + bonus) * ((1 - fw) + fw * fresh)});
  }
  if (S.sort === "rating") out.sort((a, b) => b.score - a.score || b.newest - a.newest);
  else out.sort((a, b) => b.newest - a.newest);
  return out;
}

function render() {
  buildGroups();
  const list = document.getElementById("list");
  list.textContent = "";
  const res = compute();
  const now = Date.now() / 1000;
  if (!res.length) {
    const e = el("div", "empty", "Нічого не знайдено за цими фільтрами.");
    const b = el("button", "", "Скинути фільтри");
    b.onclick = () => { S.geo = "all"; S.cat = "all"; S.q = ""; qbox.value = ""; save(); render(); };
    e.appendChild(el("br")); e.appendChild(b);
    list.appendChild(e);
  }
  const top = res.reduce((m, r) => Math.max(m, r.score), 0) || 1;
  res.slice(0, S.shown).forEach((r, idx) => {
    const c = r.c;
    const item = el("article", "item");
    const beam = el("i", "beam"); beam.style.opacity = String(0.14 + 0.86 * (r.score / top));
    beam.title = "Рейтинг сюжету";
    const num = el("div", "num" + (S.sort === "rating" && idx < 3 ? " hot" : ""), String(idx + 1));
    const body = el("div", "body");
    const a = el("a", "t", c.t);
    a.href = c.u; a.target = "_blank"; a.rel = "noopener noreferrer";
    const meta = el("div", "meta");
    meta.appendChild(el("span", "when", ago(now - r.newest)));
    meta.appendChild(el("span", "geo " + c.g, GEO_NAME[c.g] || c.g));
    const k = el("span", "cat"); k.dataset.c = c.c; k.appendChild(el("i")); k.appendChild(document.createTextNode(CAT_NAME[c.c] || c.c));
    meta.appendChild(k);
    if (r.srcs.length > 1) meta.appendChild(el("span", "cov", sources(r.srcs.length)));
    if (r.hn > 0) meta.appendChild(el("span", "hn", "HN " + r.hn + (r.hnc ? " / " + r.hnc + " комент." : "")));
    const srcs = el("span", "srcs");
    const shownSrc = {};
    for (const x of c.i) {
      if (shownSrc[x[0]] || !(x[0] in D.src)) continue;
      shownSrc[x[0]] = 1;
      const s = el("a", "chip", D.src[x[0]][0]);
      s.href = x[2]; s.target = "_blank"; s.rel = "noopener noreferrer"; srcs.appendChild(s);
    }
    meta.appendChild(srcs);
    body.appendChild(a); body.appendChild(meta);
    item.appendChild(beam); item.appendChild(num); item.appendChild(body); list.appendChild(item);
  });
  document.getElementById("more").hidden = res.length <= S.shown;
  const d = new Date(D.gen * 1000);
  document.getElementById("upd").textContent =
    "Оновлено " + d.toLocaleString("uk-UA") + "\nСюжетів: " + res.length + ", версія 7";
}

document.getElementById("more").onclick = () => { S.shown += PAGE; render(); };
const qbox = document.getElementById("q");
qbox.value = S.q;
let timer = null;
qbox.oninput = () => { clearTimeout(timer); timer = setTimeout(() => { S.q = qbox.value; S.shown = PAGE; save(); render(); toTop(); }, 200); };
render();
setTimeout(() => document.getElementById("list").classList.remove("intro"), 1500);

// ---- годинник ----
function tickClock() {
  const d = new Date();
  const p = n => String(n).padStart(2, "0");
  document.getElementById("clk-t").textContent = p(d.getHours()) + ":" + p(d.getMinutes());
  document.getElementById("clk-s").textContent = p(d.getSeconds());
  const ds = d.toLocaleDateString("uk-UA", {weekday: "long", day: "numeric", month: "long"});
  document.getElementById("clk-d").textContent = ds.charAt(0).toUpperCase() + ds.slice(1);
}
tickClock(); setInterval(tickClock, 1000);

// ---- погода в Одесі (Open-Meteo, без ключа) ----
const WX_URL = "https://api.open-meteo.com/v1/forecast?latitude=46.4825&longitude=30.7233" +
  "&current=temperature_2m,apparent_temperature,weather_code,wind_speed_10m" +
  "&daily=weather_code,temperature_2m_max,temperature_2m_min,precipitation_probability_max" +
  "&wind_speed_unit=ms&timezone=auto&forecast_days=8";
const WMO = [[[0],"☀️","Ясно"],[[1],"🌤️","Переважно ясно"],[[2],"⛅","Мінлива хмарність"],[[3],"☁️","Хмарно"],
  [[45,48],"🌫️","Туман"],[[51,53,55,56,57],"🌦️","Мряка"],[[61,63,65,66,67],"🌧️","Дощ"],
  [[71,73,75,77],"🌨️","Сніг"],[[80,81,82],"🌦️","Злива"],[[85,86],"🌨️","Снігопад"],[[95,96,99],"⛈️","Гроза"]];
function wmo(code) {
  for (const [codes, icon, text] of WMO) if (codes.includes(code)) return {icon, text};
  return {icon: "🌡️", text: ""};
}
const deg = v => (v > 0.5 ? "+" : v < -0.5 ? "−" : "") + Math.abs(Math.round(v)) + "°";
function renderWeather(w, note) {
  const box = document.getElementById("wx");
  box.textContent = "";
  const c = w.current, dl = w.daily;
  const now = el("div", "wx-now");
  const m = wmo(c.weather_code);
  now.appendChild(el("div", "wx-ico", m.icon));
  now.appendChild(el("div", "wx-t", deg(c.temperature_2m)));
  const info = el("div", "wx-d");
  const l1 = el("div"); l1.appendChild(el("b", "", "Одеса")); l1.appendChild(document.createTextNode(", " + m.text.toLowerCase()));
  info.appendChild(l1);
  info.appendChild(el("div", "", "сьогодні " + deg(dl.temperature_2m_min[0]) + " … " + deg(dl.temperature_2m_max[0]) +
    ", вітер " + Math.round(c.wind_speed_10m) + " м/с"));
  info.appendChild(el("div", "", "відчувається " + deg(c.apparent_temperature) +
    (dl.precipitation_probability_max[0] != null ? ", опади " + dl.precipitation_probability_max[0] + "%" : "") +
    (note ? ", " + note : "")));
  now.appendChild(info);
  box.appendChild(now);
  const days = el("div", "wx-days");
  for (let i = 1; i < dl.time.length; i++) {
    const d = new Date(dl.time[i] + "T12:00:00");
    const cell = el("div", "day");
    cell.appendChild(el("div", "dn", d.toLocaleDateString("uk-UA", {weekday: "short"}) + " " + d.getDate()));
    cell.appendChild(el("div", "di", wmo(dl.weather_code[i]).icon));
    const t = el("div", "dt", deg(dl.temperature_2m_max[i]));
    t.appendChild(el("span", "", " " + deg(dl.temperature_2m_min[i])));
    cell.appendChild(t);
    const pr = dl.precipitation_probability_max[i];
    cell.appendChild(el("div", "dp", pr != null ? "💧 " + pr + "%" : ""));
    cell.title = wmo(dl.weather_code[i]).text;
    days.appendChild(cell);
  }
  box.appendChild(days);
}
function wxMessage(text) {
  const box = document.getElementById("wx"); box.textContent = "";
  box.appendChild(el("span", "wx-msg", text));
}
async function loadWeather() {
  try {
    const r = await fetch(WX_URL, {cache: "no-store"});
    if (!r.ok) throw new Error("HTTP " + r.status);
    const w = await r.json();
    if (!w.current || !w.daily || !w.daily.time) throw new Error("неочікувана відповідь");
    renderWeather(w, "");
    try { localStorage.setItem("wx", JSON.stringify({t: Date.now(), w})); } catch (e) {}
  } catch (e) {
    let cached = null;
    try { cached = JSON.parse(localStorage.getItem("wx") || "null"); } catch (e2) {}
    if (cached && cached.w) {
      try { renderWeather(cached.w, "збережені дані"); return; } catch (e3) {}
    }
    wxMessage("Погода недоступна (" + e.message + ")");
  }
}
loadWeather(); setInterval(loadWeather, 30 * 60 * 1000);

// ---- керування оновленням (працює, тільки коли сторінку відкрито через програму) ----
const INTERVALS = [[15,"15 хв"],[30,"30 хв"],[60,"1 год"],[180,"3 год"],[0,"Вимк."]];
const ctl = document.getElementById("ctl");
if (!location.protocol.startsWith("http")) document.getElementById("ctl-off").hidden = false;
async function hasApp() {
  try { const r = await fetch("/status", {cache: "no-store"}); const j = await r.json(); return "interval" in j; }
  catch (e) { return false; }
}
function staticMode() {
  const o = document.getElementById("ctl-off");
  o.textContent = "Новини оновлюються автоматично приблизно раз на пів години. Сторінка перезавантажується сама.";
  o.hidden = false;
  setTimeout(() => location.reload(), 900000);
}
function startPanel() {
  ctl.hidden = false;
  const gi = document.getElementById("g-int");
  const stEl = document.getElementById("st");
  const nowBtn = document.getElementById("now");
  const lamp = document.getElementById("lamp");
  const hhmm = t => new Date(t * 1000).toLocaleTimeString("uk-UA", {hour: "2-digit", minute: "2-digit"});
  const btns = {};
  let pt = null;
  INTERVALS.forEach(([m, name]) => {
    const b = el("button", "", name);
    b.setAttribute("aria-pressed", "false");
    b.onclick = () => post("/interval?minutes=" + m);
    gi.appendChild(b); btns[m] = b;
  });
  function show(st) {
    for (const m in btns) btns[m].setAttribute("aria-pressed", String(Number(m) === st.interval));
    nowBtn.disabled = st.running;
    nowBtn.textContent = st.running ? "Оновлюю…" : "Оновити зараз";
    lamp.classList.toggle("busy", !!st.running);
    let t = "";
    if (st.running) t = "Іде збір новин.";
    else {
      if (st.last_ok) t = "Оновлено о " + hhmm(st.last_ok) + ".";
      if (st.last_error) t += " Помилка: " + st.last_error + ".";
      t += st.interval && st.next_run ? " Наступне о " + hhmm(st.next_run) + "." : " Автооновлення вимкнено.";
    }
    stEl.textContent = t.trim();
    if (st.page_gen && st.page_gen > D.gen) { location.reload(); return; }
    clearTimeout(pt); pt = setTimeout(poll, st.running ? 2000 : 15000);
  }
  async function post(url) {
    try { const r = await fetch(url, {method: "POST"}); show(await r.json()); } catch (e) { stEl.textContent = "Програма не відповідає."; }
  }
  async function poll() {
    try { const r = await fetch("/status", {cache: "no-store"}); show(await r.json()); }
    catch (e) { stEl.textContent = "Програма не відповідає, можливо, вона вимкнена."; clearTimeout(pt); pt = setTimeout(poll, 15000); }
  }
  nowBtn.onclick = () => post("/refresh");
  document.getElementById("quit").onclick = async () => {
    if (!confirm("Вимкнути програму? Автооновлення зупиниться до наступного запуску ярлика.")) return;
    try { await fetch("/quit", {method: "POST"}); } catch (e) {}
    stEl.textContent = "Програму вимкнено, вкладку можна закрити.";
  };
  poll();
}
if (location.protocol.startsWith("http")) hasApp().then(ok => ok ? startPanel() : staticMode());
else setTimeout(() => location.reload(), 900000);
</script>
</body>
</html>
'''


# ---------- запуск ----------

def main():
    base = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument("--sources", default=str(base / "sources.yaml"))
    parser.add_argument("--denylist", default=str(base / "denylist.txt"))
    parser.add_argument("--data-dir", default=str(base))
    parser.add_argument("--timeout", type=int, default=TIMEOUT_SECONDS)
    args = parser.parse_args()

    data_dir = Path(args.data_dir)
    for path in (args.sources, args.denylist):
        if not Path(path).exists():
            sys.exit(f"Не найден файл {path}")

    config = yaml.safe_load(Path(args.sources).read_text(encoding="utf-8"))
    deny_rules = load_denylist(args.denylist)
    sources = [s for s in config.get("sources", []) if s.get("feed_url") or s.get("api_url")]

    def run(source):
        if source.get("feed_url"):
            return collect_feed(source, deny_rules, args.timeout)
        return collect_hn(source, deny_rules, args.timeout)

    started = time.time()
    with ThreadPoolExecutor(max_workers=6) as pool:
        results = list(pool.map(run, sources))

    now = int(time.time())
    con = open_db(data_dir / "news.db")
    lines = [f"Сбор новостей: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}", ""]
    total_new = 0
    failed = 0
    for source, res in zip(sources, results):
        if res["error"]:
            failed += 1
            lines.append(f"[ОШИБКА] {res['name']}: {res['error']}")
            continue
        new = store(con, source, source.get("country", ""), res["items"], now)
        total_new += new
        dropped = sum(res["dropped"].values())
        lines.append(f"[ OK ] {res['name']}: в ленте {res['total']}, принято {len(res['items'])}, новых {new}")
        for reason, count in res["dropped"].items():
            lines.append(f"      отброшено {count}: {reason}")
    con.execute("DELETE FROM items WHERE published < ?", (now - KEEP_DAYS * 86400,))
    con.commit()
    changed_cats = reclassify(con, sources, now)
    if changed_cats:
        lines.append(f"Категории пересчитаны у {changed_cats} заметок")
    groups = recluster(con, now)
    con.commit()
    clusters, items = build_page(con, sources, now, data_dir / "news.html")
    con.commit()
    total_in_db = con.execute("SELECT COUNT(*) FROM items").fetchone()[0]
    con.close()

    summary = (f"Итого: новых заметок {total_new}, на странице {items} заметок в {clusters} сюжетах, "
               f"в базе {total_in_db}, лент с ошибкой {failed} из {len(sources)}, {time.time() - started:.0f} с")
    lines += ["", summary]
    text = "\n".join(lines)
    print(text)
    (data_dir / "collect_report.txt").write_text(text + "\n", encoding="utf-8-sig")
    with open(data_dir / "history.log", "a", encoding="utf-8") as log:
        log.write(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}  сбор: {summary}\n")
    sys.exit(1 if failed == len(sources) else 0)


if __name__ == "__main__":
    main()
