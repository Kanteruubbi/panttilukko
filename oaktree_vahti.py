#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Oaktree-vahti
=============
Seuraa Oaktree Capitalin osakemyyntejä ja lähettää ilmoituksen puhelimeen
(ntfy-sovellus) ja/tai sähköpostiin.

Lähteet:
  1. SEC EDGAR (USA): Form 4 (toteutuneet myynnit), Form 144 (ilmoitus aikeesta
     myydä) sekä Schedule 13D/13G -muutokset kaikilta Oaktreen nimissä
     ilmoittavilta tahoilta.
  2. Google News -haku: pakettikaupat (block trade) ja myynnit muualla
     maailmassa, esim. Euroopan ja Aasian pörsseissä.

Vain Pythonin vakiokirjasto (Python 3.8+), ei asennettavia paketteja.
Ohjeet: LUEMINUT.md

Käyttö:
  python oaktree_vahti.py            # jatkuva seuranta
  python oaktree_vahti.py --once     # yksi kierros (ajastukseen / GitHub Actions)
  python oaktree_vahti.py --test     # lähetä testi-ilmoitus
"""

import argparse
import html
import json
import os
import re
import smtplib
import ssl
import sys
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage
from email.utils import parsedate_to_datetime

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


# ---------------------------------------------------------------------------
# Asetukset (luetaan tiedostosta asetukset.env tai ympäristömuuttujista)
# ---------------------------------------------------------------------------

def load_settings_file(path):
    if not os.path.exists(path):
        return
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            key, value = line.split("=", 1)
            key = key.strip()
            value = value.strip().strip('"').strip("'")
            if key and not os.environ.get(key):
                os.environ[key] = value


load_settings_file(os.path.join(SCRIPT_DIR, "asetukset.env"))


def _env(name, default=""):
    v = os.environ.get(name, "")
    return v if v != "" else default


SEC_USER_AGENT = _env("SEC_USER_AGENT")
NTFY_TOPIC = _env("NTFY_TOPIC")
NTFY_SERVER = _env("NTFY_SERVER", "https://ntfy.sh").rstrip("/")
EMAIL_TO = _env("EMAIL_TO")
SMTP_HOST = _env("SMTP_HOST", "smtp.gmail.com")
SMTP_PORT = int(_env("SMTP_PORT", "465"))
SMTP_USER = _env("SMTP_USER")
SMTP_PASSWORD = _env("SMTP_PASSWORD").replace(" ", "")
MIN_SALE_USD = float(_env("MIN_SALE_USD", "1000000"))
ONLY_DECREASES = _env("ONLY_DECREASES", "0") == "1"
NOTIFY_NEW_POSITIONS = _env("NOTIFY_NEW_POSITIONS", "0") == "1"
WATCH_NEWS = _env("WATCH_NEWS", "1") == "1"
INTERVAL_SECONDS = max(60, int(_env("INTERVAL_SECONDS", "180")))
STATE_FILE = _env("STATE_FILE", os.path.join(SCRIPT_DIR, "oaktree_state.json"))
EXTRA_CIKS = [c.strip() for c in _env("EXTRA_CIKS").split(",") if c.strip().isdigit()]
NEWS_EXCLUDE = [s.strip().lower() for s in _env(
    "NEWS_EXCLUDE",
    "Specialty Lending,Strategic Credit,OCSL,Oaktree Acquisition,Oaktree Gardens,Oaktree Real Estate Income",
).split(",") if s.strip()]

CIK_LOOKUP_URL = "https://www.sec.gov/Archives/edgar/cik-lookup-data.txt"
SUBMISSIONS_URL = "https://data.sec.gov/submissions/CIK{cik:0>10}.json"

FORMS = {
    "4", "4/A", "144", "144/A",
    "SC 13D", "SC 13D/A", "SC 13G", "SC 13G/A",
    "SCHEDULE 13D", "SCHEDULE 13D/A", "SCHEDULE 13G", "SCHEDULE 13G/A",
}

OAKTREE_NAME = re.compile(r"\bOAKTREE\b", re.I)
FILER_RE = re.compile(r"OAKTREE|\bOCM\b", re.I)

NEWS_QUERIES = [
    ("en", '"Oaktree" (sells OR sold OR "block trade" OR placing OR bookbuild OR '
           'offloads OR "cuts stake" OR "stake sale" OR divests) when:2d'),
    ("fi", '"Oaktree" (liputusilmoitus OR myy OR myi OR osakekauppa OR osuutensa) when:7d'),
]

TX_CODES = {
    "S": "myynti markkinoilla",
    "D": "luovutus yhtiölle",
    "J": "muu luovutus (esim. jako rahaston sijoittajille)",
    "F": "verojen maksu osakkeilla",
    "G": "lahja",
    "C": "konversio",
    "X": "option käyttö",
}


# ---------------------------------------------------------------------------
# Apufunktiot
# ---------------------------------------------------------------------------

def log(msg):
    print("[{}] {}".format(datetime.now().strftime("%Y-%m-%d %H:%M:%S"), msg), flush=True)


def now_utc():
    return datetime.now(timezone.utc)


def is_due(iso_ts, delta):
    if not iso_ts:
        return True
    try:
        return now_utc() - datetime.fromisoformat(iso_ts) > delta
    except ValueError:
        return True


def num(text):
    if text is None:
        return None
    try:
        return float(str(text).replace(",", "").strip())
    except ValueError:
        return None


def fmt_int(x):
    return "{:,.0f}".format(x).replace(",", " ")


def fmt_usd(x):
    if x >= 1e9:
        return "{:.2f} miljardia dollaria".format(x / 1e9).replace(".", ",")
    if x >= 1e6:
        return "{:.1f} miljoonaa dollaria".format(x / 1e6).replace(".", ",")
    return "{} dollaria".format(fmt_int(x))


_last_sec_request = [0.0]


def http_get(url, sec=False, max_bytes=None, timeout=30, retries=3):
    headers = {
        "User-Agent": SEC_USER_AGENT if sec else "Mozilla/5.0 (compatible; Oaktree-vahti)",
        "Accept": "*/*",
    }
    last_err = None
    for attempt in range(retries):
        if sec:  # SEC sallii max 10 pyyntöä sekunnissa
            wait = 0.15 - (time.time() - _last_sec_request[0])
            if wait > 0:
                time.sleep(wait)
            _last_sec_request[0] = time.time()
        try:
            req = urllib.request.Request(url, headers=headers)
            with urllib.request.urlopen(req, timeout=timeout) as r:
                if not max_bytes:
                    return r.read()
                chunks, total = [], 0
                while total < max_bytes:
                    chunk = r.read(min(65536, max_bytes - total))
                    if not chunk:
                        break
                    chunks.append(chunk)
                    total += len(chunk)
                return b"".join(chunks)
        except urllib.error.HTTPError as e:
            if e.code == 404:
                raise
            last_err = e
            time.sleep((10 if e.code in (403, 429) else 2) * (attempt + 1))
        except (urllib.error.URLError, TimeoutError, ConnectionError, OSError) as e:
            last_err = e
            time.sleep(2 * (attempt + 1))
    raise last_err


# ---------------------------------------------------------------------------
# Ilmoitukset
# ---------------------------------------------------------------------------

def notify(title, body, url=None, priority=4):
    log("ILMOITUS: {} | {}".format(title, body.replace("\n", " / ")))
    sent = False
    if NTFY_TOPIC:
        try:
            payload = {"topic": NTFY_TOPIC, "title": title, "message": body,
                       "priority": priority, "tags": ["chart_with_downwards_trend"]}
            if url:
                payload["click"] = url
                payload["actions"] = [{"action": "view", "label": "Avaa", "url": url}]
            req = urllib.request.Request(
                NTFY_SERVER, data=json.dumps(payload).encode("utf-8"),
                headers={"Content-Type": "application/json"}, method="POST")
            urllib.request.urlopen(req, timeout=20).read()
            sent = True
        except Exception as e:
            log("  ntfy-ilmoitus epäonnistui: {}".format(e))
    if EMAIL_TO and SMTP_USER and SMTP_PASSWORD:
        try:
            msg = EmailMessage()
            msg["Subject"] = title
            msg["From"] = SMTP_USER
            msg["To"] = EMAIL_TO
            msg.set_content(body + ("\n\n" + url if url else "") + "\n\n-- Oaktree-vahti")
            ctx = ssl.create_default_context()
            if SMTP_PORT == 465:
                with smtplib.SMTP_SSL(SMTP_HOST, SMTP_PORT, context=ctx, timeout=30) as s:
                    s.login(SMTP_USER, SMTP_PASSWORD)
                    s.send_message(msg)
            else:
                with smtplib.SMTP(SMTP_HOST, SMTP_PORT, timeout=30) as s:
                    s.starttls(context=ctx)
                    s.login(SMTP_USER, SMTP_PASSWORD)
                    s.send_message(msg)
            sent = True
        except Exception as e:
            log("  sähköposti epäonnistui: {}".format(e))
    if not sent:
        log("  (Ilmoitusta ei lähetetty mihinkään – tarkista asetukset.env)")
    return sent


# ---------------------------------------------------------------------------
# Tila
# ---------------------------------------------------------------------------

def load_state():
    try:
        with open(STATE_FILE, encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def save_state(state):
    tmp = STATE_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=1, sort_keys=True)
    os.replace(tmp, STATE_FILE)


def prune_state(state):
    cut = (now_utc() - timedelta(days=45)).date().isoformat()
    state["seen"] = {k: v for k, v in state.get("seen", {}).items() if v >= cut}
    cut_news = (now_utc() - timedelta(days=14)).date().isoformat()
    state["news_seen"] = {k: v for k, v in state.get("news_seen", {}).items() if v >= cut_news}


# ---------------------------------------------------------------------------
# SEC EDGAR
# ---------------------------------------------------------------------------

def get_submissions(cik):
    data = http_get(SUBMISSIONS_URL.format(cik=cik), sec=True)
    return json.loads(data.decode("utf-8"))


def refresh_ciks(state):
    """Etsii kaikki EDGARin tunnukset (CIK), joiden nimessä on 'Oaktree'."""
    log("Päivitetään Oaktree-tunnusten lista SEC:ltä (voi kestää pari minuuttia)...")
    found = {}
    try:
        req = urllib.request.Request(CIK_LOOKUP_URL, headers={"User-Agent": SEC_USER_AGENT})
        with urllib.request.urlopen(req, timeout=600) as r:
            for raw in r:
                line = raw.decode("latin-1")
                if "OAKTREE" not in line.upper():
                    continue
                parts = line.strip().rstrip(":").rsplit(":", 1)
                if len(parts) != 2 or not parts[1].strip().isdigit():
                    continue
                name, cik = parts[0].strip(), str(int(parts[1]))
                if OAKTREE_NAME.search(name):
                    found[cik] = name
    except Exception as e:
        log("  Tunnuslistan lataus epäonnistui ({}), käytetään vanhaa listaa.".format(e))
        if state.get("ciks"):
            return
    for c in EXTRA_CIKS:
        found.setdefault(str(int(c)), "(lisätty käsin)")
    log("  Löytyi {} nimeä, tarkistetaan mitkä ovat aktiivisia...".format(len(found)))

    old = state.get("ciks", {})
    cutoff = (now_utc() - timedelta(days=730)).date().isoformat()
    result = {}
    for cik, name in found.items():
        try:
            sub = get_submissions(cik)
            dates = sub.get("filings", {}).get("recent", {}).get("filingDate", [])
            result[cik] = {"name": sub.get("name") or name,
                           "active": bool(dates) and max(dates) >= cutoff}
        except urllib.error.HTTPError as e:
            if e.code == 404:
                continue
            result[cik] = old.get(cik, {"name": name, "active": True})
        except Exception:
            result[cik] = old.get(cik, {"name": name, "active": True})
    state["ciks"] = result
    state["ciks_updated"] = now_utc().isoformat()
    log("  Seurannassa {} tunnusta, joista {} aktiivisia.".format(
        len(result), sum(1 for v in result.values() if v["active"])))


def filing_urls(cik, acc):
    base = "https://www.sec.gov/Archives/edgar/data/{}/{}/".format(int(cik), acc.replace("-", ""))
    return base + acc + ".txt", base + acc + "-index.htm"


HEADER_RE = re.compile(
    r"^([A-Z][A-Z \-]*?):\s*$\s*(?:COMPANY|OWNER) DATA:\s*COMPANY CONFORMED NAME:[ \t]*(.+?)[ \t]*$",
    re.M)


def parse_header(txt):
    end = txt.find("</SEC-HEADER>")
    head = txt[:end] if end > 0 else txt[:20000]
    subject, filers = None, []
    for label, name in HEADER_RE.findall(head):
        label = label.strip()
        if label in ("SUBJECT COMPANY", "ISSUER"):
            subject = subject or name.strip()
        else:
            filers.append(name.strip())
    return subject, filers


def first_tag(txt, tag):
    m = re.search(r"<(?:\w+:)?{0}>\s*([^<]*?)\s*</(?:\w+:)?{0}>".format(tag), txt)
    return html.unescape(m.group(1)) if m else None


def all_tags(txt, tag):
    return [html.unescape(v) for v in
            re.findall(r"<(?:\w+:)?{0}>\s*([^<]*?)\s*</(?:\w+:)?{0}>".format(tag), txt)]


def handle_form4(txt, form, subject, link):
    m = re.search(r"<ownershipDocument>.*?</ownershipDocument>", txt, re.S)
    if not m:
        return ("Oaktree {}: {}".format(form, subject),
                "Uusi sisäpiirin kaupankäynti-ilmoitus (tietoja ei voitu lukea automaattisesti).")
    root = ET.fromstring(m.group(0))
    owners = [(e.text or "") for e in root.iter("rptOwnerName")]
    if owners and not any(FILER_RE.search(o) for o in owners):
        return None  # ilmoittaja ei ole Oaktree
    issuer = root.findtext("issuer/issuerName") or subject
    symbol = (root.findtext("issuer/issuerTradingSymbol") or "").strip()

    sold_sh, sold_val, after, codes, dates, priced = 0.0, 0.0, None, set(), set(), False
    for t in root.iter("nonDerivativeTransaction"):
        ad = (t.findtext("transactionAmounts/transactionAcquiredDisposedCode/value") or "").strip()
        if ad != "D":
            continue
        sh = num(t.findtext("transactionAmounts/transactionShares/value")) or 0.0
        pr = num(t.findtext("transactionAmounts/transactionPricePerShare/value"))
        sold_sh += sh
        if pr:
            sold_val += sh * pr
            priced = True
        a = num(t.findtext("postTransactionAmounts/sharesOwnedFollowingTransaction/value"))
        if a is not None:
            after = a
        codes.add((t.findtext("transactionCoding/transactionCode") or "?").strip())
        d = t.findtext("transactionDate/value")
        if d:
            dates.add(d[:10])

    if sold_sh <= 0:
        return None  # osto tai muu kuin luovutus
    if priced and sold_val < MIN_SALE_USD:
        log("  Ohitetaan pieni myynti: {} {}".format(issuer, fmt_usd(sold_val)))
        return None

    name = "{} ({})".format(issuer, symbol) if symbol else issuer
    lines = ["Oaktree on luovuttanut {} osaketta.".format(fmt_int(sold_sh))]
    if priced:
        lines.append("Arvo noin {}, keskihinta ${:.2f}.".format(fmt_usd(sold_val), sold_val / sold_sh))
    if after is not None:
        lines.append("Omistukseen jäi {} osaketta.".format(fmt_int(after)))
    if dates:
        lines.append("Kauppapäivä(t): {}.".format(", ".join(sorted(dates))))
    lines.append("Tyyppi: " + ", ".join("{} = {}".format(c, TX_CODES.get(c, "muu")) for c in sorted(codes)))
    return "Oaktree MYI: " + name, "\n".join(lines)


def handle_form144(txt, form, subject, link):
    issuer = first_tag(txt, "issuerName") or subject
    values = [num(v) or 0 for v in all_tags(txt, "aggregateMarketValue")]
    units = [num(v) or 0 for v in all_tags(txt, "noOfUnitsSold")]
    total = sum(values)
    if total and total < MIN_SALE_USD:
        log("  Ohitetaan pieni Form 144: {} {}".format(issuer, fmt_usd(total)))
        return None
    lines = ["Oaktree on ilmoittanut AIKOVANSA myydä osakkeita (Form 144)."]
    if units:
        lines.append("Määrä: {} osaketta.".format(fmt_int(sum(units))))
    if total:
        lines.append("Arvo noin {}.".format(fmt_usd(total)))
    sale_date = first_tag(txt, "approxSaleDate")
    if sale_date:
        lines.append("Arvioitu myyntipäivä: {}.".format(sale_date))
    return "Oaktree aikoo myydä: " + issuer, "\n".join(lines)


def extract_percent(txt):
    vals = [float(v) for _, v in re.findall(
        r"<([\w:]*[Pp][Ee][Rr][Cc][Ee][Nn][Tt][\w:]*)>\s*([0-9]{1,3}(?:\.[0-9]+)?)\s*%?\s*</\1>", txt)]
    if not vals:
        plain = html.unescape(re.sub(r"<[^>]+>", " ", txt[:1500000]))
        vals = [float(v) for v in re.findall(
            r"PERCENT\s+OF\s+CLASS.{0,300}?(\d{1,3}(?:\.\d+)?)\s*%", plain, re.I | re.S)]
    vals = [v for v in vals[:40] if 0 <= v <= 100]
    return max(vals) if vals else None


def handle_13dg(state, txt, form, subject, fdate):
    pct = extract_percent(txt)
    key = (subject or "?").upper()
    prev = state.setdefault("pct", {}).get(key, {}).get("pct")
    if pct is not None:
        state["pct"][key] = {"pct": pct, "date": fdate}

    is_amendment = form.endswith("/A")
    decreased = prev is not None and pct is not None and pct < prev - 0.001
    below = pct is not None and pct < 5
    if not is_amendment and not NOTIFY_NEW_POSITIONS:
        log("  Uusi omistus (ei myynti), tallennetaan vertailukohdaksi: {} {}%".format(subject, pct))
        return None
    if ONLY_DECREASES and not (decreased or below or pct is None):
        return None

    kind = "13D" if "13D" in form else "13G"
    lines = []
    if pct is not None and prev is not None:
        lines.append("Omistusosuus {} % → {} %.".format(prev, pct))
    elif pct is not None:
        lines.append("Omistusosuus nyt noin {} %.".format(pct))
    else:
        lines.append("Omistusosuutta ei voitu lukea automaattisesti.")
    if below:
        lines.append("Osuus on alle 5 %:n ilmoitusrajan – Oaktree on myynyt suurimman osan.")
    lines.append("Ilmoitus: Schedule {} {}.".format(
        kind, "muutos" if is_amendment else "uusi"))
    title_prefix = "Oaktree VÄHENSI" if (decreased or below) else "Oaktree omistusmuutos"
    return "{}: {}".format(title_prefix, subject), "\n".join(lines)


def handle_filing(state, cik, acc, form, fdate):
    txt_url, link = filing_urls(cik, acc)
    try:
        txt = http_get(txt_url, sec=True, max_bytes=3000000).decode("utf-8", "replace")
    except Exception as e:
        notify("Oaktree {}: uusi ilmoitus".format(form),
               "Uusi SEC-ilmoitus, mutta sen luku epäonnistui ({}).".format(e), link)
        return
    subject, filers = parse_header(txt)
    if filers and not any(FILER_RE.search(f) for f in filers) and not form.startswith("4"):
        return  # joku muu on ilmoittanut Oaktreen omasta yhtiöstä
    subject = subject or "tuntematon yhtiö"
    base = form.split("/")[0]
    try:
        if base == "4":
            res = handle_form4(txt, form, subject, link)
        elif base == "144":
            res = handle_form144(txt, form, subject, link)
        else:
            res = handle_13dg(state, txt, form, subject, fdate)
    except Exception as e:
        res = ("Oaktree {}: {}".format(form, subject),
               "Uusi SEC-ilmoitus (automaattinen tulkinta epäonnistui: {}).".format(e))
    if res:
        title, body = res
        notify(title, body + "\nJätetty SEC:lle {}.".format(fdate), link, priority=5 if "MYI" in title else 4)


def check_sec(state, bootstrap):
    ciks = state.get("ciks", {})
    seen = state.setdefault("seen", {})
    include_inactive = is_due(state.get("last_inactive_check"), timedelta(days=1))
    window = (now_utc() - timedelta(days=10)).date().isoformat()
    polled = 0
    for cik, info in ciks.items():
        if not info.get("active") and not include_inactive:
            continue
        try:
            rec = get_submissions(cik).get("filings", {}).get("recent", {})
        except Exception as e:
            log("  SEC-haku epäonnistui ({} {}): {}".format(cik, info.get("name"), e))
            continue
        polled += 1
        accs, forms, dates = rec.get("accessionNumber", []), rec.get("form", []), rec.get("filingDate", [])
        for i, acc in enumerate(accs):
            fdate = dates[i]
            if fdate < window:
                break
            form = forms[i]
            if form not in FORMS or acc in seen:
                continue
            seen[acc] = fdate
            info["active"] = True
            if bootstrap:
                continue
            log("Uusi {} ({}), tunnus {}".format(form, acc, info.get("name")))
            handle_filing(state, cik, acc, form, fdate)
    if include_inactive:
        state["last_inactive_check"] = now_utc().isoformat()
    log("SEC tarkistettu ({} tunnusta).".format(polled))


# ---------------------------------------------------------------------------
# Uutiset (Google News RSS)
# ---------------------------------------------------------------------------

def news_url(lang, query):
    if lang == "fi":
        params = {"q": query, "hl": "fi", "gl": "FI", "ceid": "FI:fi"}
    else:
        params = {"q": query, "hl": "en-US", "gl": "US", "ceid": "US:en"}
    return "https://news.google.com/rss/search?" + urllib.parse.urlencode(params)


def title_key(title):
    t = re.sub(r"\s+-\s+[^-]+$", "", title)  # poista " - Lähde"
    return "t:" + re.sub(r"[^a-z0-9]+", " ", t.lower()).strip()[:120]


def check_news(state, bootstrap):
    seen = state.setdefault("news_seen", {})
    today = now_utc().date().isoformat()
    cutoff = now_utc() - timedelta(days=3)
    for lang, q in NEWS_QUERIES:
        try:
            root = ET.fromstring(http_get(news_url(lang, q)))
        except Exception as e:
            log("  Uutishaku epäonnistui: {}".format(e))
            continue
        for item in root.iter("item"):
            title = (item.findtext("title") or "").strip()
            link = (item.findtext("link") or "").strip()
            guid = (item.findtext("guid") or link).strip()
            low = title.lower()
            if "oaktree" not in low or any(x in low for x in NEWS_EXCLUDE):
                continue
            tk = title_key(title)
            if guid in seen or tk in seen:
                continue
            seen[guid] = today
            seen[tk] = today
            try:
                pub = parsedate_to_datetime(item.findtext("pubDate"))
                if pub.tzinfo is None:
                    pub = pub.replace(tzinfo=timezone.utc)
                if pub < cutoff:
                    continue
                when = pub.astimezone().strftime("%d.%m. klo %H:%M")
            except Exception:
                when = ""
            if bootstrap:
                continue
            source = item.findtext("source") or ""
            notify("Uutinen: " + title[:150],
                   "Lähde: {} {}\nTarkista, onko kyse Oaktreen myynnistä.".format(source, when).strip(),
                   link, priority=4)
    log("Uutiset tarkistettu.")


# ---------------------------------------------------------------------------
# Pääohjelma
# ---------------------------------------------------------------------------

def check_config():
    ok = True
    if not SEC_USER_AGENT or "example.com" in SEC_USER_AGENT or "@" not in SEC_USER_AGENT:
        log("VIRHE: aseta SEC_USER_AGENT (nimi ja oikea sähköpostiosoite) tiedostoon asetukset.env. "
            "SEC estää pyynnöt ilman sitä.")
        ok = False
    if not NTFY_TOPIC and not (EMAIL_TO and SMTP_USER and SMTP_PASSWORD):
        log("VAROITUS: ilmoitustapaa ei ole asetettu (NTFY_TOPIC tai sähköposti). "
            "Löydökset näkyvät vain tässä ikkunassa.")
    return ok


def run_cycle(state):
    bootstrap = not state.get("initialized")
    if bootstrap:
        log("Ensimmäinen ajo: merkitään nykyiset ilmoitukset nähdyiksi (niistä ei lähetetä hälytyksiä).")
    if not state.get("ciks") or is_due(state.get("ciks_updated"), timedelta(days=7)):
        refresh_ciks(state)
        save_state(state)
    check_sec(state, bootstrap)
    if WATCH_NEWS:
        check_news(state, bootstrap)
    prune_state(state)
    if bootstrap:
        state["initialized"] = True
        ciks = state.get("ciks", {})
        notify("Oaktree-vahti käynnistyi",
               "Seurataan {} SEC-tunnusta ({} aktiivista){}. Saat ilmoituksen uusista myynneistä.".format(
                   len(ciks), sum(1 for v in ciks.values() if v.get("active")),
                   " ja uutisia" if WATCH_NEWS else ""), priority=3)
    save_state(state)


def main():
    p = argparse.ArgumentParser(description="Oaktree-vahti")
    p.add_argument("--once", action="store_true", help="aja yksi kierros ja lopeta")
    p.add_argument("--test", action="store_true", help="lähetä testi-ilmoitus")
    args = p.parse_args()

    if args.test:
        ok = notify("Oaktree-vahti: testi", "Jos näet tämän, ilmoitukset toimivat.", priority=3)
        sys.exit(0 if ok else 1)

    if not check_config():
        sys.exit(1)

    state = load_state()
    if args.once:
        run_cycle(state)
        return

    log("Oaktree-vahti käynnissä, tarkistus {} sekunnin välein. Lopeta: Ctrl+C.".format(INTERVAL_SECONDS))
    while True:
        try:
            run_cycle(state)
        except KeyboardInterrupt:
            raise
        except Exception:
            log("Kierros epäonnistui:\n" + traceback.format_exc())
        time.sleep(INTERVAL_SECONDS)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        log("Lopetettu.")
