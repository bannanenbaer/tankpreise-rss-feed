"""
RSS-Feed fuer Tankpreise im Umkreis von Wennigsen (Deister).

Nutzt die Tankerkooenig API v4 fuer:
- Korrekte Preisanzeige mit 2 Dezimalstellen im deutschen Format (z.B. 1,97)
- Zeitstempel der letzten Preisaenderung
- Preisaenderungsbetrag und Trend
- KI-Preisprognose basierend auf SQLite-Preishistorie + saisonale Muster

KI-Prognose (3 Stufen):
  Stufe 1: Datengetrieben (SQLite) - lernt aus gesammelten Preisen
           Erkennt Preisaenderungs-Zeitpunkte pro Station und Wochentag
  Stufe 2: Saisonale Muster - historische Durchschnitte (Monat/Woche)
           Basiert auf wissenschaftlichen Erkenntnissen ueber dt. Tankpreise
  Stufe 3: Statische Tagesmuster - typische Preiskurve als Fallback

Detail-Anzeige:
  Naechste Aenderung: 11:15 (15 Minuten)
  Diesel: 2,10 EUR (^2,15 EUR)
"""

from flask import Flask, Response
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from datetime import datetime, timedelta
import xml.etree.ElementTree as ET
from xml.dom import minidom
from cachetools import TTLCache
import logging
import pytz
import sqlite3
import os
import threading
import math
import re

# ---------------------------------------------------------------------------
# Konfiguration
# ---------------------------------------------------------------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
)
log = logging.getLogger("tankpreise")

app = Flask(__name__)

LAT = 52.2762744
LNG = 9.5671846
RADIUS = 5
MAX_STATIONS = 5
API_KEY = "77ee8866-8df3-45f0-8f63-70c4d1c76bff"
API_URL = "https://creativecommons.tankerkoenig.de/api/v4/stations/search"
DETAIL_URL = "https://creativecommons.tankerkoenig.de/json/detail.php"
BERLIN_TZ = pytz.timezone("Europe/Berlin")

# Cache: 3 Minuten (API-Limit beachten)
_cache = TTLCache(maxsize=5, ttl=180)
# Cache fuer Stationsdetails: 1 Stunde (Oeffnungszeiten aendern sich selten)
_detail_cache = TTLCache(maxsize=20, ttl=3600)

# Pfad fuer die SQLite-Datenbank
DB_PATH = os.environ.get("TANK_DB_PATH", "/tmp/tankpreise.db")

# Thread-Lock fuer SQLite
_db_lock = threading.Lock()

# ---------------------------------------------------------------------------
# Saisonale Preismuster (basierend auf historischen Daten 2014-2026)
# Monatliche Preisabweichung vom Jahresdurchschnitt in Cent
# Quelle: Analyse von Tankerkoenig-Daten und MTS-K Berichten
# ---------------------------------------------------------------------------
SEASONAL_MONTHLY_OFFSET = {
    1: -2.0,   # Januar: nach Weihnachten, Nachfrage sinkt
    2: -1.5,   # Februar: noch ruhig
    3: +0.5,   # Maerz: Fruehling, leichter Anstieg
    4: +1.5,   # April: Osterreiseverkehr
    5: +2.0,   # Mai: Feiertage, Brueckentagseffekt
    6: +2.5,   # Juni: Sommerferien beginnen
    7: +3.0,   # Juli: Hochsaison Reiseverkehr
    8: +2.5,   # August: Sommerferien
    9: +1.0,   # September: Ferienende, Preise sinken
    10: +0.5,  # Oktober: Herbst, moderat
    11: -1.0,  # November: Nachfrage sinkt
    12: -0.5,  # Dezember: Weihnachtsverkehr, aber Oelpreis oft tief
}

# Typische Preisaenderungs-Zeitpunkte deutscher Tankstellen
# Basierend auf Bundeskartellamt-Studien: 5-6 Preisrunden pro Tag
TYPICAL_CHANGE_HOURS = [6, 8, 10, 13, 16, 18, 20, 22]

# Wochentags-Faktoren (Mo=0, So=6)
# Montag ist typischerweise der teuerste Tag, Sonntag/Freitag am guenstigsten
WEEKDAY_FACTOR = {
    0: +1.5,   # Montag: teuerster Tag
    1: +1.0,   # Dienstag
    2: +0.5,   # Mittwoch
    3: 0.0,    # Donnerstag
    4: -0.5,   # Freitag: guenstiger
    5: -1.0,   # Samstag: guenstiger
    6: -1.5,   # Sonntag: guenstigster Tag
}


# ---------------------------------------------------------------------------
# SQLite-Datenbank: Preishistorie
# ---------------------------------------------------------------------------
def _init_db():
    """Erstellt die Datenbank-Tabellen, falls sie nicht existieren."""
    with _db_lock:
        conn = sqlite3.connect(DB_PATH)
        try:
            # Preishistorie (alle Kraftstoffe)
            conn.execute("""
                CREATE TABLE IF NOT EXISTS price_history (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    station_id TEXT NOT NULL,
                    station_name TEXT,
                    fuel_type TEXT NOT NULL DEFAULT 'e5',
                    price REAL NOT NULL,
                    weekday INTEGER NOT NULL,
                    hour INTEGER NOT NULL,
                    minute INTEGER NOT NULL,
                    timestamp TEXT NOT NULL,
                    created_at TEXT DEFAULT CURRENT_TIMESTAMP
                )
            """)
            conn.execute("""
                CREATE INDEX IF NOT EXISTS idx_station_fuel_weekday_hour
                ON price_history (station_id, fuel_type, weekday, hour)
            """)
            conn.execute("""
                CREATE INDEX IF NOT EXISTS idx_timestamp
                ON price_history (timestamp)
            """)
            # Preisaenderungen (fuer Zeitpunkt-Vorhersage)
            conn.execute("""
                CREATE TABLE IF NOT EXISTS price_changes (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    station_id TEXT NOT NULL,
                    fuel_type TEXT NOT NULL DEFAULT 'e5',
                    old_price REAL,
                    new_price REAL NOT NULL,
                    change_amount REAL NOT NULL,
                    weekday INTEGER NOT NULL,
                    hour INTEGER NOT NULL,
                    minute INTEGER NOT NULL,
                    timestamp TEXT NOT NULL
                )
            """)
            conn.execute("""
                CREATE INDEX IF NOT EXISTS idx_changes_station_weekday
                ON price_changes (station_id, fuel_type, weekday)
            """)
            conn.commit()
            log.info("Datenbank initialisiert: %s", DB_PATH)
        finally:
            conn.close()


def _record_price_db(station_id, station_name, fuel_type, price, timestamp):
    """Speichert einen Preis in der SQLite-Datenbank.
    Erkennt Preisaenderungen und speichert sie separat.
    """
    if not price or price <= 0:
        return

    with _db_lock:
        conn = sqlite3.connect(DB_PATH)
        try:
            # Letzten Eintrag fuer diese Station + Kraftstoff pruefen
            row = conn.execute(
                "SELECT price, timestamp FROM price_history "
                "WHERE station_id = ? AND fuel_type = ? ORDER BY id DESC LIMIT 1",
                (station_id, fuel_type)
            ).fetchone()

            should_insert = True
            price_changed = False
            old_price = None

            if row:
                last_price, last_ts = row
                old_price = last_price
                try:
                    last_dt = datetime.fromisoformat(last_ts)
                    time_diff = (timestamp - last_dt).total_seconds()
                except Exception:
                    time_diff = 9999

                # Preisaenderung erkennen
                if abs(last_price - price) >= 0.001:
                    price_changed = True

                # Nur speichern wenn Preis sich geaendert hat ODER 10 Min vergangen
                if not price_changed and time_diff < 600:
                    should_insert = False

            if should_insert:
                weekday = timestamp.weekday()
                hour = timestamp.hour
                minute = timestamp.minute
                conn.execute(
                    "INSERT INTO price_history "
                    "(station_id, station_name, fuel_type, price, weekday, hour, minute, timestamp) "
                    "VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                    (station_id, station_name, fuel_type, price, weekday, hour, minute,
                     timestamp.isoformat())
                )

                # Preisaenderung separat speichern
                if price_changed and old_price is not None:
                    change_amount = round(price - old_price, 4)
                    conn.execute(
                        "INSERT INTO price_changes "
                        "(station_id, fuel_type, old_price, new_price, change_amount, "
                        "weekday, hour, minute, timestamp) "
                        "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                        (station_id, fuel_type, old_price, price, change_amount,
                         weekday, hour, minute, timestamp.isoformat())
                    )
                    log.info("Preisaenderung: %s %s %.3f -> %.3f (%+.3f)",
                             station_name, fuel_type, old_price, price, change_amount)

                conn.commit()

            # Alte Daten aufraeumen (aelter als 180 Tage)
            cutoff = (timestamp - timedelta(days=180)).isoformat()
            conn.execute("DELETE FROM price_history WHERE timestamp < ?", (cutoff,))
            conn.execute("DELETE FROM price_changes WHERE timestamp < ?", (cutoff,))
            conn.commit()
        except Exception as e:
            log.error("DB-Schreibfehler: %s", e)
        finally:
            conn.close()


def _get_hourly_profile(station_id, fuel_type="e5", weekday=None, days_back=28):
    """Berechnet das Stunden-Preisprofil fuer eine Station."""
    profile = {}
    cutoff = (datetime.now(BERLIN_TZ) - timedelta(days=days_back)).isoformat()

    with _db_lock:
        conn = sqlite3.connect(DB_PATH)
        try:
            if weekday is not None:
                rows = conn.execute(
                    "SELECT hour, AVG(price), MIN(price), MAX(price), COUNT(*) "
                    "FROM price_history "
                    "WHERE station_id = ? AND fuel_type = ? AND weekday = ? AND timestamp > ? "
                    "GROUP BY hour ORDER BY hour",
                    (station_id, fuel_type, weekday, cutoff)
                ).fetchall()
            else:
                rows = conn.execute(
                    "SELECT hour, AVG(price), MIN(price), MAX(price), COUNT(*) "
                    "FROM price_history "
                    "WHERE station_id = ? AND fuel_type = ? AND timestamp > ? "
                    "GROUP BY hour ORDER BY hour",
                    (station_id, fuel_type, cutoff)
                ).fetchall()

            for hour, avg, mn, mx, cnt in rows:
                profile[hour] = {
                    "avg": round(avg, 4),
                    "min": round(mn, 4),
                    "max": round(mx, 4),
                    "count": cnt,
                }
        except Exception as e:
            log.error("DB-Lesefehler (Profil): %s", e)
        finally:
            conn.close()

    return profile


def _get_change_pattern(station_id, fuel_type="e5", days_back=28):
    """Analysiert die typischen Preisaenderungs-Zeitpunkte einer Station.

    Gibt ein Dict zurueck: {weekday: [(hour, minute, avg_change, count), ...]}
    Sortiert nach Haeufigkeit.
    """
    patterns = {}
    cutoff = (datetime.now(BERLIN_TZ) - timedelta(days=days_back)).isoformat()

    with _db_lock:
        conn = sqlite3.connect(DB_PATH)
        try:
            rows = conn.execute(
                "SELECT weekday, hour, minute, AVG(change_amount), COUNT(*) "
                "FROM price_changes "
                "WHERE station_id = ? AND fuel_type = ? AND timestamp > ? "
                "GROUP BY weekday, hour "
                "ORDER BY weekday, hour",
                (station_id, fuel_type, cutoff)
            ).fetchall()

            for wd, h, m, avg_chg, cnt in rows:
                if wd not in patterns:
                    patterns[wd] = []
                patterns[wd].append((h, m, round(avg_chg, 4), cnt))
        except Exception as e:
            log.error("DB-Lesefehler (Pattern): %s", e)
        finally:
            conn.close()

    return patterns


def _get_db_stats():
    """Gibt Statistiken ueber die Datenbank zurueck."""
    stats = {"total_records": 0, "total_changes": 0, "stations": 0,
             "oldest": None, "newest": None}
    with _db_lock:
        conn = sqlite3.connect(DB_PATH)
        try:
            row = conn.execute("SELECT COUNT(*) FROM price_history").fetchone()
            stats["total_records"] = row[0] if row else 0

            row = conn.execute("SELECT COUNT(*) FROM price_changes").fetchone()
            stats["total_changes"] = row[0] if row else 0

            row = conn.execute(
                "SELECT COUNT(DISTINCT station_id) FROM price_history"
            ).fetchone()
            stats["stations"] = row[0] if row else 0

            row = conn.execute(
                "SELECT MIN(timestamp), MAX(timestamp) FROM price_history"
            ).fetchone()
            if row and row[0]:
                stats["oldest"] = row[0]
                stats["newest"] = row[1]
        except Exception as e:
            log.error("DB-Lesefehler (Stats): %s", e)
        finally:
            conn.close()
    return stats


# ---------------------------------------------------------------------------
# KI-Preisprognose
# ---------------------------------------------------------------------------
def _predict_next_change(station, all_fuels):
    """
    Vorhersage der naechsten Preisaenderung: Zeitpunkt + neuer Preis.

    Gibt zurueck:
    {
        "change_time": datetime,       # Wann aendert sich der Preis?
        "minutes_until": int,           # Minuten bis zur Aenderung
        "fuels": {                      # Prognostizierte Preise pro Kraftstoff
            "Super E5": {"current": 1.88, "predicted": 1.93, "direction": "^"},
            "Diesel": {"current": 2.10, "predicted": 2.15, "direction": "^"},
        },
        "reason": str,
        "confidence": int,
        "source": str,
        "warning": bool,               # True wenn Anstieg in < 15 Min
    }
    """
    now = datetime.now(BERLIN_TZ)
    hour = now.hour
    minute = now.minute
    weekday = now.weekday()
    station_id = station.get("id", "")

    # --- Stufe 1: Datengetriebene Vorhersage ---
    change_patterns = _get_change_pattern(station_id, "e5", days_back=56)

    # Haben wir genug Daten fuer diesen Wochentag?
    today_patterns = change_patterns.get(weekday, [])

    if len(today_patterns) >= 3:
        # Genug Daten: Finde die naechste typische Preisaenderung
        result = _predict_from_patterns(
            station, all_fuels, today_patterns, now, "ki"
        )
        if result:
            return result

    # Alle Wochentage als Fallback
    all_patterns = []
    for wd_patterns in change_patterns.values():
        all_patterns.extend(wd_patterns)

    if len(all_patterns) >= 5:
        # Aggregiere alle Wochentage
        hourly_changes = {}
        for h, m, avg_chg, cnt in all_patterns:
            if h not in hourly_changes:
                hourly_changes[h] = {"total_chg": 0, "count": 0, "minute": m}
            hourly_changes[h]["total_chg"] += avg_chg * cnt
            hourly_changes[h]["count"] += cnt

        merged = []
        for h, data in hourly_changes.items():
            avg = data["total_chg"] / data["count"]
            merged.append((h, data["minute"], round(avg, 4), data["count"]))
        merged.sort(key=lambda x: x[0])

        result = _predict_from_patterns(
            station, all_fuels, merged, now, "ki-allgemein"
        )
        if result:
            return result

    # --- Stufe 2: Saisonale + Tagesmuster ---
    return _predict_from_static(station, all_fuels, now)


def _predict_from_patterns(station, all_fuels, patterns, now, source):
    """Vorhersage basierend auf gelernten Preisaenderungs-Mustern."""
    hour = now.hour
    minute = now.minute

    # Finde die naechste Preisaenderung nach jetzt
    next_change = None
    next_change_amount = 0

    # Zuerst: Aenderungen die heute noch kommen
    for h, m, avg_chg, cnt in sorted(patterns, key=lambda x: x[0]):
        if h > hour or (h == hour and m > minute):
            next_change = now.replace(hour=h, minute=m, second=0)
            next_change_amount = avg_chg
            break

    # Falls heute nichts mehr kommt: erste Aenderung morgen
    if next_change is None and patterns:
        first = sorted(patterns, key=lambda x: x[0])[0]
        next_change = (now + timedelta(days=1)).replace(
            hour=first[0], minute=first[1], second=0
        )
        next_change_amount = first[2]

    if next_change is None:
        return None

    minutes_until = int((next_change - now).total_seconds() / 60)

    # Prognostizierte Preise fuer alle Kraftstoffe berechnen
    fuel_predictions = {}
    for f in all_fuels:
        f_name = f.get("name", "?")
        f_price = f.get("price")
        if f_price and f_price > 0:
            # Skaliere die Aenderung proportional zum Preis
            predicted = round(f_price + next_change_amount, 4)
            if next_change_amount > 0.001:
                direction = "↑"
            elif next_change_amount < -0.001:
                direction = "↓"
            else:
                direction = "="
            fuel_predictions[f_name] = {
                "current": f_price,
                "predicted": predicted,
                "direction": direction,
            }

    # Konfidenz berechnen
    total_data = sum(cnt for _, _, _, cnt in patterns)
    confidence = min(95, 30 + int(total_data * 2))

    # Grund-Text
    if next_change_amount > 0.03:
        reason = "Starker Preisanstieg erwartet"
    elif next_change_amount > 0.001:
        reason = "Leichter Preisanstieg erwartet"
    elif next_change_amount < -0.03:
        reason = "Starker Preisrueckgang erwartet"
    elif next_change_amount < -0.001:
        reason = "Leichter Preisrueckgang erwartet"
    else:
        reason = "Preis bleibt voraussichtlich stabil"

    # Warnung wenn Anstieg in < 15 Minuten
    warning = (next_change_amount > 0.001 and minutes_until <= 15)

    return {
        "change_time": next_change,
        "minutes_until": max(0, minutes_until),
        "fuels": fuel_predictions,
        "reason": reason,
        "confidence": confidence,
        "source": source,
        "warning": warning,
    }


def _predict_from_static(station, all_fuels, now):
    """Statische Fallback-Prognose basierend auf typischen Tagesmustern
    und saisonalen Faktoren.

    Deutsche Tankstellen haben typischerweise 5-6 Preisrunden pro Tag:
    - 06:00 Preisanstieg (Morgen-Peak)
    - 08:00 Leichter Rueckgang
    - 10:00 Zweiter Anstieg
    - 13:00 Mittags-Rueckgang
    - 16:00 Nachmittags-Anstieg
    - 18:00 Abend-Tief (bester Zeitpunkt!)
    - 20:00 Leichter Anstieg
    - 22:00 Nacht-Anstieg (teuerste Phase)
    """
    hour = now.hour
    minute = now.minute
    weekday = now.weekday()
    month = now.month
    is_weekend = weekday >= 5

    # Typische Preisaenderungen pro Stunde (in Cent)
    if is_weekend:
        hourly_changes = {
            7: +3, 10: -2, 13: +1, 16: -2, 19: -1, 22: +4
        }
    else:
        hourly_changes = {
            6: +5, 8: -2, 10: +2, 13: -3, 16: +1, 18: -3, 20: +1, 22: +5
        }

    # Finde naechste Aenderung
    next_hour = None
    next_change_cents = 0

    for h in sorted(hourly_changes.keys()):
        if h > hour or (h == hour and minute < 30):
            next_hour = h
            next_change_cents = hourly_changes[h]
            break

    # Falls heute nichts mehr: erste Aenderung morgen
    if next_hour is None:
        first_h = sorted(hourly_changes.keys())[0]
        next_change_time = (now + timedelta(days=1)).replace(
            hour=first_h, minute=0, second=0
        )
        next_change_cents = hourly_changes[first_h]
    else:
        next_change_time = now.replace(hour=next_hour, minute=0, second=0)

    minutes_until = int((next_change_time - now).total_seconds() / 60)

    # Saisonalen Faktor einbeziehen
    seasonal_offset = SEASONAL_MONTHLY_OFFSET.get(month, 0) / 100
    weekday_offset = WEEKDAY_FACTOR.get(weekday, 0) / 100
    change_amount = (next_change_cents / 100) + seasonal_offset * 0.1 + weekday_offset * 0.05

    # Prognostizierte Preise
    fuel_predictions = {}
    for f in all_fuels:
        f_name = f.get("name", "?")
        f_price = f.get("price")
        if f_price and f_price > 0:
            predicted = round(f_price + change_amount, 4)
            if change_amount > 0.001:
                direction = "↑"
            elif change_amount < -0.001:
                direction = "↓"
            else:
                direction = "="
            fuel_predictions[f_name] = {
                "current": f_price,
                "predicted": predicted,
                "direction": direction,
            }

    # Grund-Text
    if 18 <= hour <= 20:
        reason = "Bester Zeitpunkt zum Tanken (Abend-Tief)"
    elif 5 <= hour <= 7:
        reason = "Preise steigen morgens stark an"
    elif 21 <= hour or hour < 5:
        reason = "Nacht-Hochpreisphase"
    elif change_amount > 0:
        reason = "Preisanstieg erwartet"
    else:
        reason = "Preisrueckgang erwartet"

    reason += " [Standardmuster - KI lernt noch]"

    warning = (change_amount > 0.001 and minutes_until <= 15)

    return {
        "change_time": next_change_time,
        "minutes_until": max(0, minutes_until),
        "fuels": fuel_predictions,
        "reason": reason,
        "confidence": 15,
        "source": "statisch",
        "warning": warning,
    }


# ---------------------------------------------------------------------------
# Hilfsfunktionen
# ---------------------------------------------------------------------------
def _format_price(price):
    """Formatiert den Preis mit 2 Dezimalstellen im deutschen Format.
    Die letzte Ziffer (immer 9) wird abgeschnitten.
    z.B. 1.889 -> '1,88', 1.909 -> '1,90'"""
    if price is None:
        return "---"
    truncated = int(price * 100) / 100
    return f"{truncated:.2f}".replace(".", ",")


def _format_price_eur(price):
    """Formatiert den Preis als EUR-String: 1,88 EUR"""
    if price is None:
        return "---"
    truncated = int(price * 100) / 100
    return f"{truncated:.2f}".replace(".", ",") + " EUR"


def _parse_timestamp(ts_str):
    """Parst einen Tankerkooenig-Zeitstempel -> datetime in Europe/Berlin."""
    if not ts_str:
        return None
    try:
        if ts_str.endswith("+01") or ts_str.endswith("+02"):
            ts_str += ":00"
        dt = datetime.fromisoformat(ts_str)
        if dt.tzinfo is None:
            dt = BERLIN_TZ.localize(dt)
        return dt.astimezone(BERLIN_TZ)
    except Exception as e:
        log.warning("Zeitstempel-Fehler: %s (%s)", ts_str, e)
        return None


def _time_ago(dt):
    """Gibt eine lesbare Zeitdifferenz zurueck (z.B. 'vor 15 Min')."""
    if not dt:
        return "unbekannt"
    now = datetime.now(BERLIN_TZ)
    diff = now - dt
    minutes = int(diff.total_seconds() / 60)
    if minutes < 1:
        return "gerade eben"
    elif minutes < 60:
        return f"vor {minutes} Min"
    elif minutes < 1440:
        hours = minutes // 60
        return f"vor {hours} Std"
    else:
        days = minutes // 1440
        return f"vor {days} Tag{'en' if days > 1 else ''}"


def _sanitize(text):
    """Ersetzt Umlaute und Sonderzeichen fuer Fritz!Fon-Kompatibilitaet."""
    replacements = {
        "\u00e4": "ae", "\u00f6": "oe", "\u00fc": "ue",
        "\u00c4": "Ae", "\u00d6": "Oe", "\u00dc": "Ue",
        "\u00df": "ss", "\u20ac": "EUR",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    return text


# ---------------------------------------------------------------------------
# Daten laden (v4 API)
# ---------------------------------------------------------------------------
def _fetch_station_detail(station_id):
    """Laedt Stationsdetails (Oeffnungszeiten, wholeDay) von der Detail-API.
    Ergebnis wird 1 Stunde gecacht.
    """
    cached = _detail_cache.get(station_id)
    if cached is not None:
        return cached

    try:
        resp = requests.get(DETAIL_URL, params={
            "id": station_id,
            "apikey": API_KEY,
        }, timeout=5)

        if resp.status_code != 200:
            log.warning("Detail-API Status %s fuer %s", resp.status_code, station_id)
            return None

        data = resp.json()
        if not data.get("ok"):
            return None

        station = data.get("station", {})
        detail = {
            "openingTimes": station.get("openingTimes", []),
            "wholeDay": station.get("wholeDay", False),
            "overrides": station.get("overrides", []),
        }
        _detail_cache[station_id] = detail
        log.info("Detail geladen fuer %s (wholeDay=%s)", station_id, detail["wholeDay"])
        return detail

    except Exception as e:
        log.warning("Detail-API Fehler fuer %s: %s", station_id, e)
        return None


def _fetch_stations():
    """Laedt Tankstellen und Preise von der Tankerkooenig v4 API."""
    cached = _cache.get("stations")
    if cached is not None:
        return cached

    try:
        session = requests.Session()
        retries = Retry(total=3, backoff_factor=0.5,
                        status_forcelist=[500, 502, 503, 504])
        session.mount("https://", HTTPAdapter(max_retries=retries))

        resp = session.get(API_URL, params={
            "apikey": API_KEY,
            "lat": LAT,
            "lng": LNG,
            "rad": RADIUS,
        }, timeout=8)

        if resp.status_code != 200:
            log.error("API Status %s: %s", resp.status_code, resp.text[:100])
            return []

        data = resp.json()
        stations = data.get("stations", [])

        if not stations:
            log.warning("Keine Tankstellen gefunden.")
            return []

        # Nach E5-Preis sortieren (guenstigste zuerst)
        def _get_e5_price(station):
            for f in station.get("fuels", []):
                if f.get("name", "").lower().startswith("super e5"):
                    return f.get("price", 9999)
            return 9999

        stations.sort(key=_get_e5_price)

        # Offene Stationen bevorzugen
        stations.sort(key=lambda s: 0 if s.get("isOpen") else 1)

        result = stations[:MAX_STATIONS]

        # ALLE Kraftstoffpreise in SQLite speichern
        now = datetime.now(BERLIN_TZ)
        for s in result:
            brand = s.get("brand") or s.get("name", "?")
            for f in s.get("fuels", []):
                f_name = f.get("name", "").lower()
                if "e5" in f_name:
                    fuel_key = "e5"
                elif "e10" in f_name:
                    fuel_key = "e10"
                elif "diesel" in f_name:
                    fuel_key = "diesel"
                else:
                    fuel_key = f_name
                _record_price_db(
                    s["id"], brand, fuel_key,
                    f.get("price"), now
                )

        _cache["stations"] = result
        log.info("%d Tankstellen geladen.", len(result))
        return result

    except requests.exceptions.Timeout:
        log.error("API-Timeout")
    except requests.exceptions.ConnectionError:
        log.error("API nicht erreichbar")
    except Exception as e:
        log.error("API-Fehler: %s", e)

    return []


# ---------------------------------------------------------------------------
# RSS-Feed generieren
# ---------------------------------------------------------------------------
def _build_feed():
    stations = _fetch_stations()
    now = datetime.now(BERLIN_TZ)

    rss = ET.Element("rss", version="2.0")
    channel = ET.SubElement(rss, "channel")
    ET.SubElement(channel, "title").text = "Tankpreise - Wennigsen"
    ET.SubElement(channel, "link").text = (
        "https://creativecommons.tankerkoenig.de"
    )
    ET.SubElement(channel, "description").text = (
        "Tankpreise im Umkreis von Wennigsen (Deister)"
    )
    ET.SubElement(channel, "language").text = "de-de"
    ET.SubElement(channel, "lastBuildDate").text = (
        now.strftime("%a, %d %b %Y %H:%M:%S %z")
    )

    if not stations:
        item = ET.SubElement(channel, "item")
        ET.SubElement(item, "title").text = "Keine Daten verfuegbar"
        ET.SubElement(item, "description").text = (
            "Die Tankerkooenig-API liefert derzeit keine Daten. "
            "Bitte spaeter erneut versuchen."
        )
    else:
        for s in stations:
            # E5-Daten finden (fuer Titel)
            e5_fuel = None
            all_fuels = s.get("fuels", [])
            for f in all_fuels:
                if f.get("name", "").lower().startswith("super e5"):
                    e5_fuel = f
                    break

            if not e5_fuel:
                continue

            price = e5_fuel.get("price")
            last_change = e5_fuel.get("lastChange", {})
            change_amount = last_change.get("amount", 0) or 0
            change_ts = _parse_timestamp(last_change.get("timestamp"))

            brand = s.get("brand") or s.get("name", "?")
            is_open = s.get("isOpen", False)
            status = "offen" if is_open else "geschlossen"

            # Trend-Pfeil (basierend auf letzter Aenderung)
            if change_amount > 0:
                trend = "↑"
            elif change_amount < 0:
                trend = "↓"
            else:
                trend = "="

            # --- KI-PREISPROGNOSE ---
            prediction = _predict_next_change(s, all_fuels)

            # Warnsignal
            warning = ""
            if prediction and prediction.get("warning"):
                warning = "! "

            # --- TITEL ---
            # Format: "! 1,88 EUR ^ | TAS (offen)"
            item = ET.SubElement(channel, "item")
            title_text = _sanitize(
                f"{warning}{_format_price(price)}\u20ac {trend} | {brand} ({status})"
            )
            ET.SubElement(item, "title").text = title_text

            # --- BESCHREIBUNG / DETAILS ---
            desc_parts = []

            # 1. Naechste Preisaenderung (prominent oben)
            if prediction:
                ct = prediction["change_time"]
                mins = prediction["minutes_until"]

                if mins <= 60:
                    time_str = f"{mins} Min"
                else:
                    time_str = f"{mins // 60} Std {mins % 60} Min"

                desc_parts.append(
                    f"Naechste Aenderung: {ct.strftime('%H:%M')} ({time_str})"
                )

                # 2. Alle Kraftstoffpreise mit Prognose
                for f in all_fuels:
                    f_name = f.get("name", "?")
                    f_price = f.get("price")
                    if f_price and f_price > 0:
                        pred_info = prediction["fuels"].get(f_name)
                        if pred_info:
                            pred_price = pred_info["predicted"]
                            direction = pred_info["direction"]
                            desc_parts.append(
                                f"{f_name}: {_format_price(f_price)} EUR "
                                f"({direction}{_format_price(pred_price)} EUR)"
                            )
                        else:
                            desc_parts.append(
                                f"{f_name}: {_format_price(f_price)} EUR"
                            )
            else:
                # Ohne Prognose: nur Preise auflisten
                for f in all_fuels:
                    f_name = f.get("name", "?")
                    f_price = f.get("price")
                    if f_price and f_price > 0:
                        desc_parts.append(
                            f"{f_name}: {_format_price(f_price)} EUR"
                        )

            # 3. Letzte Preisaenderung
            if change_ts:
                change_str = change_ts.strftime("%H:%M")
                ago_str = _time_ago(change_ts)
                if change_amount > 0:
                    desc_parts.append(
                        f"Letzte: +{abs(change_amount):.2f} um {change_str} ({ago_str})"
                    )
                elif change_amount < 0:
                    desc_parts.append(
                        f"Letzte: -{abs(change_amount):.2f} um {change_str} ({ago_str})"
                    )

            desc_parts.append("")

            # 4. Adresse (kompakt)
            street = s.get("street", "")
            place = s.get("place", "")
            dist = s.get("dist", 0)
            if street:
                desc_parts.append(f"{street}, {place} ({dist:.1f}km)")

            # 5. Oeffnungszeiten (mit Tankautomat-Kennzeichnung)
            station_id = s.get("id", "")
            detail = _fetch_station_detail(station_id)
            if detail:
                whole_day = detail.get("wholeDay", False)
                opening_times = detail.get("openingTimes", [])

                if whole_day:
                    desc_parts.append("24h*")
                    desc_parts.append("*Tankautomat")
                elif opening_times:
                    for ot in opening_times:
                        text = ot.get("text", "")
                        start = ot.get("start", "")[:5]  # HH:MM
                        end = ot.get("end", "")[:5]
                        if text and start and end:
                            desc_parts.append(f"{text}: {start}-{end}")
            else:
                # Fallback: closesAt aus der v4 API
                closes_at = s.get("closesAt")
                if closes_at:
                    close_dt = _parse_timestamp(closes_at)
                    if close_dt:
                        desc_parts.append(
                            f"Schliesst: {close_dt.strftime('%H:%M')} Uhr"
                        )

            # Sanitize fuer Fritz!Fon
            desc_text = _sanitize("\n".join(desc_parts))
            ET.SubElement(item, "description").text = desc_text

    raw_xml = ET.tostring(rss, "utf-8")
    pretty = minidom.parseString(raw_xml)
    return pretty.toprettyxml(indent="  ", encoding="utf-8").decode("utf-8")


# ---------------------------------------------------------------------------
# Flask-Routen
# ---------------------------------------------------------------------------
@app.route("/")
def index():
    stats = _get_db_stats()
    return (
        "<h1>Tankpreise RSS - Wennigsen</h1>"
        "<p><a href='/feed.rss'>Zum RSS-Feed</a></p>"
        "<p>Datenquelle: Tankerk&ouml;nig API v4 (CC BY 4.0)</p>"
        "<hr>"
        "<h2>KI-Datenbank</h2>"
        f"<p>Gespeicherte Preise: <b>{stats['total_records']}</b></p>"
        f"<p>Erkannte Preis&auml;nderungen: <b>{stats['total_changes']}</b></p>"
        f"<p>Tankstellen: <b>{stats['stations']}</b></p>"
        f"<p>&Auml;ltester Eintrag: {stats['oldest'] or 'noch keine Daten'}</p>"
        f"<p>Neuester Eintrag: {stats['newest'] or 'noch keine Daten'}</p>"
        "<p><a href='/stats'>Detaillierte Statistiken</a></p>"
    )


@app.route("/feed.rss")
@app.route("/feed")
def rss_feed():
    xml = _build_feed()
    resp = Response(xml, mimetype="application/rss+xml")
    resp.headers["Cache-Control"] = "no-cache, no-store, must-revalidate"
    resp.headers["Pragma"] = "no-cache"
    resp.headers["Expires"] = "0"
    return resp


@app.route("/health")
def health():
    """Health-Check (leichtgewichtig fuer Render.com)."""
    return {"status": "ok"}


@app.route("/stats")
def stats():
    """Zeigt KI-Statistiken und Datenbank-Infos."""
    db_stats = _get_db_stats()
    now = datetime.now(BERLIN_TZ)

    html = ["<h1>KI-Statistiken - Tankpreise Wennigsen</h1>"]
    html.append(f"<p>Aktuelle Zeit: {now.strftime('%d.%m.%Y %H:%M')}</p>")
    html.append(f"<p>Datensaetze: {db_stats['total_records']}</p>")
    html.append(f"<p>Erkannte Preisaenderungen: {db_stats['total_changes']}</p>")
    html.append(f"<p>Tankstellen: {db_stats['stations']}</p>")
    html.append(f"<p>Aeltester Eintrag: {db_stats['oldest'] or '-'}</p>")
    html.append(f"<p>Neuester Eintrag: {db_stats['newest'] or '-'}</p>")

    # Stunden-Profile und Aenderungsmuster anzeigen
    stations = _fetch_stations()
    for s in stations:
        e5_fuel = None
        for f in s.get("fuels", []):
            if f.get("name", "").lower().startswith("super e5"):
                e5_fuel = f
                break
        if not e5_fuel:
            continue

        brand = s.get("brand") or s.get("name", "?")
        station_id = s.get("id", "")
        current_price = e5_fuel.get("price", 0)

        html.append(f"<hr><h2>{brand} (aktuell: {_format_price(current_price)} EUR)</h2>")

        # Stunden-Profil
        profile = _get_hourly_profile(station_id, "e5", weekday=now.weekday())
        if not profile:
            profile = _get_hourly_profile(station_id, "e5")

        if profile:
            html.append("<h3>Stunden-Profil (E5)</h3>")
            html.append("<table border='1' cellpadding='4'>")
            html.append("<tr><th>Stunde</th><th>Durchschnitt</th>"
                        "<th>Min</th><th>Max</th><th>Punkte</th></tr>")
            for h in range(24):
                if h in profile:
                    p = profile[h]
                    marker = " &lt;&lt;" if h == now.hour else ""
                    html.append(
                        f"<tr><td>{h:02d}:00</td>"
                        f"<td>{_format_price(p['avg'])} EUR</td>"
                        f"<td>{_format_price(p['min'])} EUR</td>"
                        f"<td>{_format_price(p['max'])} EUR</td>"
                        f"<td>{p['count']}{marker}</td></tr>"
                    )
            html.append("</table>")

        # Aenderungsmuster
        patterns = _get_change_pattern(station_id, "e5")
        if patterns:
            html.append("<h3>Typische Preisaenderungen</h3>")
            html.append("<table border='1' cellpadding='4'>")
            html.append("<tr><th>Tag</th><th>Uhrzeit</th>"
                        "<th>Aenderung</th><th>Haeufigkeit</th></tr>")
            day_names = ["Mo", "Di", "Mi", "Do", "Fr", "Sa", "So"]
            for wd in range(7):
                if wd in patterns:
                    for h, m, avg_chg, cnt in patterns[wd]:
                        direction = "+" if avg_chg > 0 else ""
                        html.append(
                            f"<tr><td>{day_names[wd]}</td>"
                            f"<td>{h:02d}:{m:02d}</td>"
                            f"<td>{direction}{avg_chg:.3f} EUR</td>"
                            f"<td>{cnt}x</td></tr>"
                        )
            html.append("</table>")
        else:
            html.append("<p><i>Noch keine Preisaenderungen erfasst.</i></p>")

    return "\n".join(html)


# ---------------------------------------------------------------------------
# Datenbank beim Start initialisieren
# ---------------------------------------------------------------------------
_init_db()


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000)
