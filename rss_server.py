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
API_KEY = os.environ.get("TANKERKOENIG_API_KEY", "")
if not API_KEY:
    raise RuntimeError(
        "Umgebungsvariable TANKERKOENIG_API_KEY ist nicht gesetzt. "
        "Bitte in .env oder Systemumgebung setzen."
    )
API_URL = "https://creativecommons.tankerkoenig.de/api/v4/stations/search"
DETAIL_URL = "https://creativecommons.tankerkoenig.de/json/detail.php"
BERLIN_TZ = pytz.timezone("Europe/Berlin")

# Cache: 3 Minuten (API-Limit beachten)
_cache = TTLCache(maxsize=5, ttl=180)
# Cache fuer Stationsdetails: 1 Stunde (Oeffnungszeiten aendern sich selten)
_detail_cache = TTLCache(maxsize=20, ttl=3600)
# Letztes DB-Cleanup (nur einmal taeglich ausfuehren)
_last_db_cleanup = None

# ---------------------------------------------------------------------------
# Statische Shop-Oeffnungszeiten fuer Tankautomaten-Stationen
# Quelle: raiffeisen.com/standorte/6214 (Stand: Maerz 2026)
# ---------------------------------------------------------------------------
# Sommer: April-Oktober, Winter: November-Maerz
_SHOP_HOURS = {
    "7080eeac-ac6d-4807-9b23-7c20abb525ac": {  # Raiffeisen Holtensen
        # Quelle: raiffeisen.com/standorte/6214 (Stand: Maerz 2026)
        "tankstelle": [
            "Mo-Fr: 06:00-20:00",
            "Sa: 07:00-20:00 (S) / 19:00 (W)",
            "So & Feiertage: 08:00-19:00",
        ],
    },
}

# Pfad fuer die SQLite-Datenbank (Standard: Projektverzeichnis, konfigurierbar per Env)
_DEFAULT_DB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tankpreise.db")
DB_PATH = os.environ.get("TANK_DB_PATH", _DEFAULT_DB_PATH)

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

            # Alte Daten aufraeumen (aelter als 180 Tage) - nur einmal taeglich
            global _last_db_cleanup
            today = timestamp.date()
            if _last_db_cleanup != today:
                cutoff = (timestamp - timedelta(days=180)).isoformat()
                conn.execute("DELETE FROM price_history WHERE timestamp < ?", (cutoff,))
                conn.execute("DELETE FROM price_changes WHERE timestamp < ?", (cutoff,))
                conn.commit()
                _last_db_cleanup = today
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


def _get_fuel_key(f_name):
    """Mapt Kraftstoff-Anzeigenamen auf DB-Key (e5 / diesel / e10)."""
    f_lower = f_name.lower()
    if "e5" in f_lower:
        return "e5"
    elif "e10" in f_lower:
        return "e10"
    elif "diesel" in f_lower:
        return "diesel"
    return None


def _get_change_pattern(station_id, fuel_type="e5", days_back=28, all_stations=False):
    """Analysiert die typischen Preisaenderungs-Zeitpunkte.

    station_id: spezifische Station oder None (wird ignoriert wenn all_stations=True)
    all_stations: True => alle Stationen gemeinsam auswerten (mehr Datenpunkte)

    Gibt ein Dict zurueck: {weekday: [(hour, minute, avg_change, count), ...]}
    Neuere Daten werden staerker gewichtet (Halbwertszeit: 14 Tage).
    Extreme Ausreisser (>15 Ct Aenderung) werden ignoriert.
    """
    HALFLIFE_DAYS = 14.0
    OUTLIER_THRESHOLD = 0.15  # > 15 Cent = einmaliger Markteffekt, kein Tagesmuster
    patterns = {}
    cutoff = (datetime.now(BERLIN_TZ) - timedelta(days=days_back)).isoformat()
    now_dt = datetime.now(BERLIN_TZ)

    with _db_lock:
        conn = sqlite3.connect(DB_PATH)
        try:
            if all_stations:
                rows = conn.execute(
                    "SELECT weekday, hour, minute, change_amount, timestamp "
                    "FROM price_changes "
                    "WHERE fuel_type = ? AND timestamp > ? "
                    "ORDER BY weekday, hour",
                    (fuel_type, cutoff)
                ).fetchall()
            else:
                rows = conn.execute(
                    "SELECT weekday, hour, minute, change_amount, timestamp "
                    "FROM price_changes "
                    "WHERE station_id = ? AND fuel_type = ? AND timestamp > ? "
                    "ORDER BY weekday, hour",
                    (station_id, fuel_type, cutoff)
                ).fetchall()

            # Gewichtete Aggregation pro (Wochentag, Stunde)
            groups = {}
            for wd, h, m, chg, ts in rows:
                # Extreme Ausreisser ignorieren (z.B. Steuererhohungen, Marktschocks)
                if abs(chg) > OUTLIER_THRESHOLD:
                    continue
                key = (wd, h)
                if key not in groups:
                    groups[key] = {"w_sum": 0.0, "w_total": 0.0, "minutes": [], "count": 0}
                try:
                    ts_dt = datetime.fromisoformat(ts)
                    if ts_dt.tzinfo is None:
                        ts_dt = ts_dt.replace(tzinfo=BERLIN_TZ)
                    days_old = max(0.0, (now_dt - ts_dt).total_seconds() / 86400)
                except Exception:
                    days_old = days_back
                # Exponentieller Abfall: Halbwertszeit 14 Tage
                weight = 0.5 ** (days_old / HALFLIFE_DAYS)
                groups[key]["w_sum"] += chg * weight
                groups[key]["w_total"] += weight
                groups[key]["minutes"].append(m)
                groups[key]["count"] += 1

            for (wd, h), data in groups.items():
                if data["w_total"] > 0:
                    weighted_avg = data["w_sum"] / data["w_total"]
                    avg_minute = int(sum(data["minutes"]) / len(data["minutes"]))
                    if wd not in patterns:
                        patterns[wd] = []
                    patterns[wd].append((h, avg_minute, round(weighted_avg, 4), data["count"]))

            for wd in patterns:
                patterns[wd].sort(key=lambda x: x[0])

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
            "Super E5": {"current": 1.88, "predicted": 1.93},
            "Diesel": {"current": 2.10, "predicted": 2.15},
        },
        "reason": str,
        "confidence": int,
        "source": str,
        "warning": bool,               # True wenn Anstieg in < 15 Min
    }
    """
    now = datetime.now(BERLIN_TZ)
    weekday = now.weekday()
    station_id = station.get("id", "")

    # Kraftstoff-spezifische Muster fuer alle DB-Typen laden
    def _build_fuel_patterns_dict(sid, days, global_mode=False):
        return {
            ft: _get_change_pattern(sid, ft, days_back=days, all_stations=global_mode)
            for ft in ("e5", "diesel", "e10")
        }

    def _all_wd_patterns(fp_dict):
        """Aggregiert alle Wochentage stunden-gewichtet."""
        all_pats = []
        for wd_pats in fp_dict.get("e5", {}).values():
            all_pats.extend(wd_pats)
        if not all_pats:
            return []
        hourly = {}
        for h, m, avg_chg, cnt in all_pats:
            if h not in hourly:
                hourly[h] = {"w_sum": 0.0, "w_total": 0.0, "minutes": [], "count": 0}
            hourly[h]["w_sum"] += avg_chg * cnt
            hourly[h]["w_total"] += cnt
            hourly[h]["minutes"].append(m)
            hourly[h]["count"] += cnt
        merged = []
        for h, data in hourly.items():
            avg = data["w_sum"] / data["w_total"]
            avg_m = int(sum(data["minutes"]) / len(data["minutes"]))
            merged.append((h, avg_m, round(avg, 4), data["count"]))
        merged.sort(key=lambda x: x[0])
        return merged

    # --- Stufe 1: Stations-spezifisch, heutiger Wochentag ---
    fp = _build_fuel_patterns_dict(station_id, days=56)
    today_patterns = fp["e5"].get(weekday, [])

    if len(today_patterns) >= 3:
        result = _predict_from_patterns(
            station, all_fuels, today_patterns, now, "ki",
            fuel_patterns_dict={ft: pats.get(weekday, []) for ft, pats in fp.items()}
        )
        if result:
            return result

    # --- Stufe 2: Stations-spezifisch, alle Wochentage ---
    merged = _all_wd_patterns(fp)
    if len(merged) >= 3:
        result = _predict_from_patterns(
            station, all_fuels, merged, now, "ki-allgemein",
            fuel_patterns_dict={ft: sum(pats.values(), []) for ft, pats in fp.items()}
        )
        if result:
            return result

    # --- Stufe 3: Alle Stationen gemeinsam (mehr Datenpunkte) ---
    fp_global = _build_fuel_patterns_dict(station_id, days=56, global_mode=True)
    today_global = fp_global["e5"].get(weekday, [])

    if len(today_global) >= 5:
        result = _predict_from_patterns(
            station, all_fuels, today_global, now, "ki-global",
            fuel_patterns_dict={ft: pats.get(weekday, []) for ft, pats in fp_global.items()}
        )
        if result:
            return result

    merged_global = _all_wd_patterns(fp_global)
    if len(merged_global) >= 3:
        result = _predict_from_patterns(
            station, all_fuels, merged_global, now, "ki-global",
            fuel_patterns_dict={ft: sum(pats.values(), []) for ft, pats in fp_global.items()}
        )
        if result:
            return result

    # --- Stufe 4: Statisches Tagesmuster ---
    return _predict_from_static(station, all_fuels, now)


def _predict_from_patterns(station, all_fuels, patterns, now, source, fuel_patterns_dict=None):
    """Vorhersage basierend auf gelernten Preisaenderungs-Mustern.

    fuel_patterns_dict: {db_key: [(h, m, avg_chg, cnt), ...]} fuer kraftstoff-spezifische Deltas.
    Wenn nicht angegeben, wird das Delta aus `patterns` (E5) fuer alle Kraftstoffe genutzt.
    """
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
    next_hour = next_change.hour

    # Prognostizierte Preise: kraftstoff-spezifisches Delta wenn vorhanden
    fuel_predictions = {}
    for f in all_fuels:
        f_name = f.get("name", "?")
        f_price = f.get("price")
        if f_price and f_price > 0:
            delta = next_change_amount  # E5-Fallback
            if fuel_patterns_dict:
                fuel_key = _get_fuel_key(f_name)
                if fuel_key and fuel_key in fuel_patterns_dict:
                    # Naechste Aenderung dieses Kraftstoffs zur selben Stunde suchen
                    for fh, fm, fchg, fcnt in fuel_patterns_dict[fuel_key]:
                        if fh == next_hour:
                            delta = fchg
                            break
            predicted = round(f_price + delta, 4)
            fuel_predictions[f_name] = {
                "current": f_price,
                "predicted": predicted,
            }

    # Konfidenz: log-Skala + Abzug fuer aggregierte Quellen
    total_data = sum(cnt for _, _, _, cnt in patterns)
    log_factor = int(math.log1p(total_data) * 15)  # log1p(33)~3.5 -> 52; log1p(100)~4.6 -> 69
    base_confidence = min(90, 25 + log_factor)
    # Abzug wenn wir ueber alle Wochentage aggregieren mussten
    if source == "ki-allgemein":
        base_confidence = int(base_confidence * 0.85)
    elif source == "ki-global":
        base_confidence = int(base_confidence * 0.75)
    confidence = max(20, base_confidence)

    # Repraesentativ fuer die Warnung: groessten Anstieg aller Kraftstoffe pruefen
    max_delta = max(
        (pred["predicted"] - pred["current"] for pred in fuel_predictions.values()),
        default=next_change_amount
    )

    # Grund-Text (basiert auf E5-Referenz-Delta)
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
    warning = (max_delta > 0.001 and minutes_until <= 15)

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
        if h > hour:
            next_hour = h
            next_change_cents = hourly_changes[h]
            break
        elif h == hour and minute < 5:
            # Wenn wir gerade erst in der Stunde sind, koennte die Aenderung noch kommen
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

    # Saisonalen Faktor einbeziehen (Werte in Cent -> EUR, dann gewichtet addieren)
    seasonal_eur = SEASONAL_MONTHLY_OFFSET.get(month, 0) / 100
    weekday_eur = WEEKDAY_FACTOR.get(weekday, 0) / 100
    change_amount = (next_change_cents / 100) + seasonal_eur * 0.3 + weekday_eur * 0.2

    # Prognostizierte Preise
    fuel_predictions = {}
    for f in all_fuels:
        f_name = f.get("name", "?")
        f_price = f.get("price")
        if f_price and f_price > 0:
            predicted = round(f_price + change_amount, 4)
            fuel_predictions[f_name] = {
                "current": f_price,
                "predicted": predicted,
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
            # Detail-API fuer wholeDay (Tankautomat) nutzen
            station_id = s.get("id", "")
            detail = _fetch_station_detail(station_id)
            is_whole_day = detail.get("wholeDay", False) if detail else False
            
            if is_open:
                status = "offen"
            elif is_whole_day:
                status = "geschlossen / Tankautomat"
            else:
                status = "geschlossen"

            # Trend-Pfeil (basierend auf letzter Aenderung)
            if change_amount > 0:
                trend = "(+)"
            elif change_amount < 0:
                trend = "(-)"
            else:
                trend = "(=)"

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
                            # Reihenfolge: aktuell -> prognose (chronologisch korrekt)
                            if pred_price > f_price:
                                detail_line = f"{f_name}: {_format_price(f_price)} EUR -> {_format_price(pred_price)} EUR (+)"
                            elif pred_price < f_price:
                                detail_line = f"{f_name}: {_format_price(f_price)} EUR -> {_format_price(pred_price)} EUR (-)"
                            else:
                                # Preis bleibt gleich
                                detail_line = f"{f_name}: {_format_price(f_price)} EUR (gleich)"
                            
                            desc_parts.append(detail_line)
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

            # 5. Oeffnungszeiten (kompakt, mit Tankautomat-Kennzeichnung)
            if detail:
                whole_day = detail.get("wholeDay", False)
                opening_times = detail.get("openingTimes", [])
                star = "*" if whole_day else ""

                if opening_times:
                    # Saubere Logik: Oeffnungszeiten gruppieren und kompakt anzeigen
                    # Ziel: Mo-Sa: 06:00-22:00 / So & Feiertage: 07:00-22:00
                    _DAY_ORDER = ["Mo", "Di", "Mi", "Do", "Fr", "Sa", "So"]
                    _DAY_ALIASES = {
                        "montag": "Mo", "dienstag": "Di", "mittwoch": "Mi",
                        "donnerstag": "Do", "freitag": "Fr", "samstag": "Sa",
                        "sonntag": "So", "feiertag": "Feiertag",
                        "mo": "Mo", "di": "Di", "mi": "Mi", "do": "Do",
                        "fr": "Fr", "sa": "Sa", "so": "So",
                    }
                    _GROUP_ALIASES = {
                        "taeglich ausser sonn- und feiertagen": ["Mo","Di","Mi","Do","Fr","Sa"],
                        "taeglich ausser sonn": ["Mo","Di","Mi","Do","Fr","Sa"],
                        "werktags": ["Mo","Di","Mi","Do","Fr","Sa"],
                        "wochentags": ["Mo","Di","Mi","Do","Fr"],
                        "taeglich": ["Mo","Di","Mi","Do","Fr","Sa","So"],
                    }

                    # Schritt 1: Jeden Eintrag parsen -> {time_key: set(days), feiertage_times: set}
                    day_to_time = {}   # "Mo" -> "06:00-22:00"
                    feiertag_times = set()

                    for ot in opening_times:
                        text = (ot.get("text", "") or "").strip()
                        start = (ot.get("start", "") or "")[:5]
                        end = (ot.get("end", "") or "")[:5]
                        if not start or not end:
                            continue
                        time_key = f"{start}-{end}"
                        text_lower = text.lower().strip()
                        # Umlaute normalisieren fuer Vergleich
                        text_lower = text_lower.replace("ä", "ae").replace("ö", "oe").replace("ü", "ue")

                        # Gruppen-Aliase pruefen (z.B. "werktags")
                        matched_group = None
                        for alias, days_list in _GROUP_ALIASES.items():
                            if alias in text_lower:
                                matched_group = days_list
                                break

                        if matched_group:
                            for d in matched_group:
                                day_to_time[d] = time_key
                        elif "feiertag" in text_lower:
                            feiertag_times.add(time_key)
                        else:
                            # Einzelne Tage suchen
                            for alias, day_abbr in _DAY_ALIASES.items():
                                if alias in text_lower and day_abbr != "Feiertag":
                                    day_to_time[day_abbr] = time_key

                    # Schritt 2: Fehlende Wochentage mit Referenzzeit auffuellen
                    # (nur Mo-Sa, nicht So - So hat oft eigene Zeiten)
                    ref_time = None
                    for d in ["Mo", "Di", "Mi", "Do", "Fr"]:
                        if d in day_to_time:
                            ref_time = day_to_time[d]
                            break
                    if ref_time:
                        for d in ["Mo", "Di", "Mi", "Do", "Fr", "Sa"]:
                            if d not in day_to_time:
                                day_to_time[d] = ref_time
                        # So nur ergaenzen wenn keine eigene Zeit und keine Feiertags-Zeit
                        if "So" not in day_to_time and not feiertag_times:
                            day_to_time["So"] = ref_time

                    # Schritt 3: Zeiten -> Tage gruppieren
                    time_to_days = {}
                    for d, t in day_to_time.items():
                        if t not in time_to_days:
                            time_to_days[t] = []
                        if d not in time_to_days[t]:
                            time_to_days[t].append(d)

                    # Schritt 4: Ausgabe-Zeilen bauen
                    final_lines = []

                    def _days_to_range(days):
                        """Wandelt eine Liste von Tagen in Bereichs-Strings um."""
                        sorted_days = sorted(days, key=lambda d: _DAY_ORDER.index(d) if d in _DAY_ORDER else 99)
                        ranges = []
                        i = 0
                        while i < len(sorted_days):
                            start_idx = _DAY_ORDER.index(sorted_days[i])
                            end_idx = start_idx
                            while (i + 1 < len(sorted_days) and
                                   _DAY_ORDER.index(sorted_days[i + 1]) == end_idx + 1):
                                end_idx += 1
                                i += 1
                            if start_idx == end_idx:
                                ranges.append(_DAY_ORDER[start_idx])
                            else:
                                ranges.append(f"{_DAY_ORDER[start_idx]}-{_DAY_ORDER[end_idx]}")
                            i += 1
                        return ", ".join(ranges)

                    for time_key in sorted(time_to_days.keys()):
                        days = time_to_days[time_key]
                        # Trenne Mo-Sa von So
                        weekday_days = [d for d in days if d != "So"]
                        has_sunday = "So" in days

                        # Pruefen ob Feiertage die gleiche Zeit haben
                        feiertag_same_time = time_key in feiertag_times

                        if weekday_days and has_sunday and not feiertag_same_time and not feiertag_times:
                            # Mo-So alle gleich, keine Feiertage -> Mo-So zusammenfassen
                            all_days = weekday_days + ["So"]
                            day_str = _days_to_range(all_days)
                            final_lines.append(f"{day_str}: {time_key}{star}")
                        elif weekday_days:
                            day_str = _days_to_range(weekday_days)
                            final_lines.append(f"{day_str}: {time_key}{star}")

                            if has_sunday:
                                if feiertag_same_time:
                                    # So und Feiertage haben die gleiche Zeit -> zusammenfassen
                                    final_lines.append(f"So & Feiertage: {time_key}{star}")
                                    feiertag_times.discard(time_key)
                                # else: So hat gleiche Zeit wie Mo-Sa, Feiertage separat -> So weglassen
                        elif has_sunday:
                            # Nur So in dieser Gruppe (keine Wochentage)
                            if feiertag_same_time:
                                final_lines.append(f"So & Feiertage: {time_key}{star}")
                                feiertag_times.discard(time_key)
                            else:
                                final_lines.append(f"So: {time_key}{star}")

                    # Restliche Feiertags-Zeiten (andere Zeit als So)
                    for ft in sorted(feiertag_times):
                        final_lines.append(f"So & Feiertage: {ft}{star}")

                    # Sortiere nach erstem Tag
                    def _sort_key(line):
                        for d in _DAY_ORDER:
                            if line.startswith(d):
                                return _DAY_ORDER.index(d)
                        return 99

                    for line in sorted(final_lines, key=_sort_key):
                        desc_parts.append(line)

                elif whole_day:
                    desc_parts.append(f"24h Tankautomat{star}")

                if whole_day:
                    # Statische Tankstellen-Oeffnungszeiten anzeigen (falls vorhanden)
                    shop_info = _SHOP_HOURS.get(station_id)
                    if shop_info and "tankstelle" in shop_info:
                        for line in shop_info["tankstelle"]:
                            desc_parts.append(line)
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
