"""
RSS-Feed fuer Tankpreise im Umkreis von Wennigsen (Deister).

Nutzt die Tankerkooenig API v4 fuer:
- Korrekte Preisanzeige mit 2 Dezimalstellen im deutschen Format (z.B. 1,97)
- Zeitstempel der letzten Preisaenderung
- Preisaenderungsbetrag und Trend
- KI-Preisprognose basierend auf SQLite-Preishistorie

KI-Prognose:
  Speichert jeden abgerufenen Preis in einer SQLite-Datenbank.
  Analysiert die Preishistorie der letzten Wochen, um fuer jede Stunde
  und jeden Wochentag den typischen Preis zu berechnen.
  Vergleicht den aktuellen Preis mit dem historischen Durchschnitt
  der naechsten Stunden, um Preisaenderungen vorherzusagen.

1-Cent-Problem behoben:
  Alte API lieferte z.B. 1.889, Code zeigte "1.89" (gerundet auf 2 Stellen).
  Neu: Letzte Ziffer (immer 9) wird abgeschnitten -> "1,88" statt "1,89".
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
FUEL_TYPE = "e5"
MAX_STATIONS = 5
API_KEY = "77ee8866-8df3-45f0-8f63-70c4d1c76bff"
API_URL = "https://creativecommons.tankerkoenig.de/api/v4/stations/search"
BERLIN_TZ = pytz.timezone("Europe/Berlin")

# Cache: 3 Minuten (API-Limit beachten)
_cache = TTLCache(maxsize=5, ttl=180)

# Pfad fuer die SQLite-Datenbank (persistiert auf Render.com Disk)
DB_PATH = os.environ.get("TANK_DB_PATH", "/tmp/tankpreise.db")

# Thread-Lock fuer SQLite (nur ein Schreibzugriff gleichzeitig)
_db_lock = threading.Lock()


# ---------------------------------------------------------------------------
# SQLite-Datenbank: Preishistorie
# ---------------------------------------------------------------------------
def _init_db():
    """Erstellt die Datenbank-Tabellen, falls sie nicht existieren."""
    with _db_lock:
        conn = sqlite3.connect(DB_PATH)
        try:
            conn.execute("""
                CREATE TABLE IF NOT EXISTS price_history (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    station_id TEXT NOT NULL,
                    station_name TEXT,
                    price REAL NOT NULL,
                    weekday INTEGER NOT NULL,
                    hour INTEGER NOT NULL,
                    minute INTEGER NOT NULL,
                    timestamp TEXT NOT NULL,
                    created_at TEXT DEFAULT CURRENT_TIMESTAMP
                )
            """)
            conn.execute("""
                CREATE INDEX IF NOT EXISTS idx_station_weekday_hour
                ON price_history (station_id, weekday, hour)
            """)
            conn.execute("""
                CREATE INDEX IF NOT EXISTS idx_timestamp
                ON price_history (timestamp)
            """)
            conn.commit()
            log.info("Datenbank initialisiert: %s", DB_PATH)
        finally:
            conn.close()


def _record_price_db(station_id, station_name, price, timestamp):
    """Speichert einen Preis in der SQLite-Datenbank.
    Speichert nur, wenn sich der Preis seit dem letzten Eintrag geaendert hat
    oder mindestens 10 Minuten vergangen sind (um Stabilphasen zu erfassen).
    """
    if not price or price <= 0:
        return

    with _db_lock:
        conn = sqlite3.connect(DB_PATH)
        try:
            # Letzten Eintrag fuer diese Station pruefen
            row = conn.execute(
                "SELECT price, timestamp FROM price_history "
                "WHERE station_id = ? ORDER BY id DESC LIMIT 1",
                (station_id,)
            ).fetchone()

            should_insert = True
            if row:
                last_price, last_ts = row
                try:
                    last_dt = datetime.fromisoformat(last_ts)
                    time_diff = (timestamp - last_dt).total_seconds()
                except Exception:
                    time_diff = 9999

                # Nur speichern wenn Preis sich geaendert hat ODER 10 Min vergangen
                if abs(last_price - price) < 0.001 and time_diff < 600:
                    should_insert = False

            if should_insert:
                weekday = timestamp.weekday()  # 0=Mo, 6=So
                hour = timestamp.hour
                minute = timestamp.minute
                conn.execute(
                    "INSERT INTO price_history "
                    "(station_id, station_name, price, weekday, hour, minute, timestamp) "
                    "VALUES (?, ?, ?, ?, ?, ?, ?)",
                    (station_id, station_name, price, weekday, hour, minute,
                     timestamp.isoformat())
                )
                conn.commit()

            # Alte Daten aufraeumen (aelter als 90 Tage)
            cutoff = (timestamp - timedelta(days=90)).isoformat()
            conn.execute(
                "DELETE FROM price_history WHERE timestamp < ?", (cutoff,)
            )
            conn.commit()
        except Exception as e:
            log.error("DB-Schreibfehler: %s", e)
        finally:
            conn.close()


def _get_hourly_profile(station_id, weekday=None, days_back=28):
    """Berechnet das Stunden-Preisprofil fuer eine Station.

    Gibt ein Dict zurueck: {hour: {"avg": float, "min": float, "max": float, "count": int}}
    Wenn weekday angegeben, nur Daten dieses Wochentags.
    """
    profile = {}
    cutoff = (datetime.now(BERLIN_TZ) - timedelta(days=days_back)).isoformat()

    with _db_lock:
        conn = sqlite3.connect(DB_PATH)
        try:
            if weekday is not None:
                rows = conn.execute(
                    "SELECT hour, AVG(price), MIN(price), MAX(price), COUNT(*) "
                    "FROM price_history "
                    "WHERE station_id = ? AND weekday = ? AND timestamp > ? "
                    "GROUP BY hour ORDER BY hour",
                    (station_id, weekday, cutoff)
                ).fetchall()
            else:
                rows = conn.execute(
                    "SELECT hour, AVG(price), MIN(price), MAX(price), COUNT(*) "
                    "FROM price_history "
                    "WHERE station_id = ? AND timestamp > ? "
                    "GROUP BY hour ORDER BY hour",
                    (station_id, cutoff)
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


def _get_recent_changes(station_id, hours_back=24):
    """Gibt die letzten Preisaenderungen einer Station zurueck.

    Gibt eine Liste von (timestamp, price, change) zurueck,
    wobei change die Differenz zum vorherigen Preis ist.
    """
    changes = []
    cutoff = (datetime.now(BERLIN_TZ) - timedelta(hours=hours_back)).isoformat()

    with _db_lock:
        conn = sqlite3.connect(DB_PATH)
        try:
            rows = conn.execute(
                "SELECT timestamp, price FROM price_history "
                "WHERE station_id = ? AND timestamp > ? "
                "ORDER BY timestamp ASC",
                (station_id, cutoff)
            ).fetchall()

            prev_price = None
            for ts_str, price in rows:
                change = 0.0
                if prev_price is not None:
                    change = round(price - prev_price, 4)
                if change != 0 or prev_price is None:
                    changes.append((ts_str, price, change))
                prev_price = price
        except Exception as e:
            log.error("DB-Lesefehler (Changes): %s", e)
        finally:
            conn.close()

    return changes


def _get_db_stats():
    """Gibt Statistiken ueber die Datenbank zurueck."""
    stats = {"total_records": 0, "stations": 0, "oldest": None, "newest": None}
    with _db_lock:
        conn = sqlite3.connect(DB_PATH)
        try:
            row = conn.execute("SELECT COUNT(*) FROM price_history").fetchone()
            stats["total_records"] = row[0] if row else 0

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
# KI-Preisprognose (datengetrieben)
# ---------------------------------------------------------------------------
def _predict_price(station, fuel_data):
    """
    KI-Preisprognose basierend auf historischen Daten aus der SQLite-DB.

    Strategie:
    1. Lade das Stunden-Preisprofil der Station (gleicher Wochentag, letzte 4 Wochen)
    2. Falls nicht genug Daten: Fallback auf alle Wochentage
    3. Falls immer noch nicht genug: Fallback auf statische Tagesmuster
    4. Vergleiche aktuellen Preis mit dem Durchschnitt der naechsten Stunden
    5. Berechne die erwartete Preisaenderung und den Zeitpunkt
    """
    now = datetime.now(BERLIN_TZ)
    hour = now.hour
    weekday = now.weekday()
    station_id = station.get("id", "")
    current_price = fuel_data.get("price", 0)
    last_change = fuel_data.get("lastChange", {})
    change_amount = last_change.get("amount", 0) or 0

    if not current_price:
        return None

    # --- Schritt 1: Stunden-Profil laden (gleicher Wochentag) ---
    profile = _get_hourly_profile(station_id, weekday=weekday, days_back=28)

    # Mindestens 5 verschiedene Stunden mit je 2 Datenpunkten?
    data_quality = sum(1 for h in profile if profile[h]["count"] >= 2)

    # --- Schritt 2: Fallback auf alle Wochentage ---
    if data_quality < 5:
        profile = _get_hourly_profile(station_id, weekday=None, days_back=28)
        data_quality = sum(1 for h in profile if profile[h]["count"] >= 2)

    # --- Schritt 3: Fallback auf statische Muster ---
    if data_quality < 5:
        return _predict_price_static(current_price, hour, weekday, change_amount, now)

    # --- Schritt 4: Datengetriebene Prognose ---
    # Finde den erwarteten Preis fuer die naechsten 1-6 Stunden
    best_prediction = None
    best_change = 0
    best_hour_offset = 1

    for offset in range(1, 7):
        future_hour = (hour + offset) % 24
        if future_hour in profile and profile[future_hour]["count"] >= 2:
            expected_avg = profile[future_hour]["avg"]
            expected_change = round(expected_avg - current_price, 4)

            # Erste signifikante Aenderung finden (> 0.5 Cent)
            if abs(expected_change) > 0.005 and best_prediction is None:
                best_prediction = expected_avg
                best_change = expected_change
                best_hour_offset = offset

    # Wenn keine signifikante Aenderung gefunden: stabil
    if best_prediction is None:
        # Pruefen ob der aktuelle Preis unter dem Tagesdurchschnitt liegt
        all_avgs = [profile[h]["avg"] for h in profile if profile[h]["count"] >= 2]
        if all_avgs:
            day_avg = sum(all_avgs) / len(all_avgs)
            diff_to_avg = current_price - day_avg
            if diff_to_avg < -0.02:
                reason = "Preis liegt unter dem Tagesdurchschnitt - guter Zeitpunkt"
            elif diff_to_avg > 0.02:
                reason = "Preis liegt ueber dem Tagesdurchschnitt"
            else:
                reason = "Preis ist stabil (nahe am Durchschnitt)"
        else:
            reason = "Preis ist aktuell stabil"

        return {
            "price": current_price,
            "change": 0,
            "time": now + timedelta(hours=2),
            "reason": reason,
            "source": "ki",
            "confidence": _calc_confidence(profile, hour),
        }

    # --- Schritt 5: Ergebnis zusammenbauen ---
    next_change_time = now + timedelta(hours=best_hour_offset)

    # Grund-Text generieren
    if best_change > 0.03:
        reason = "Starker Preisanstieg erwartet (historisch belegt)"
    elif best_change > 0:
        reason = "Leichter Preisanstieg erwartet"
    elif best_change < -0.03:
        reason = "Starker Preisrueckgang erwartet - abwarten lohnt sich"
    else:
        reason = "Leichter Preisrueckgang erwartet"

    # Aktuellen Trend einbeziehen
    if change_amount > 0.01:
        reason += " (aktuell steigend)"
        best_change = best_change * 1.1  # Trend verstaerkt Prognose
    elif change_amount < -0.01:
        reason += " (aktuell fallend)"
        best_change = best_change * 1.1

    predicted_price = round(current_price + best_change, 4)

    return {
        "price": predicted_price,
        "change": round(best_change, 4),
        "time": next_change_time,
        "reason": reason,
        "source": "ki",
        "confidence": _calc_confidence(profile, hour),
    }


def _calc_confidence(profile, current_hour):
    """Berechnet die Konfidenz der Prognose (0-100%).
    Basiert auf der Datenmenge und -abdeckung.
    """
    if not profile:
        return 0

    # Wie viele Stunden haben Daten?
    hours_covered = sum(1 for h in profile if profile[h]["count"] >= 2)
    coverage = hours_covered / 24.0

    # Wie viele Datenpunkte insgesamt?
    total_points = sum(profile[h]["count"] for h in profile)
    data_score = min(1.0, total_points / 500)  # 500 Punkte = 100%

    # Hat die aktuelle Stunde Daten?
    current_hour_score = 1.0 if current_hour in profile and profile[current_hour]["count"] >= 3 else 0.5

    confidence = int((coverage * 0.3 + data_score * 0.4 + current_hour_score * 0.3) * 100)
    return min(100, max(0, confidence))


def _predict_price_static(current_price, hour, weekday, change_amount, now):
    """Statische Fallback-Prognose, wenn nicht genug historische Daten vorhanden.

    Basiert auf den typischen Preismustern deutscher Tankstellen:
    - 05:00-09:00: Preise steigen stark (Berufsverkehr)
    - 09:00-12:00: Erste Entspannung
    - 12:00-15:00: Kleiner Mittags-Peak
    - 15:00-18:00: Kontinuierlicher Abfall
    - 18:00-21:00: Tiefpunkt (bester Zeitpunkt)
    - 21:00-05:00: Preise steigen wieder massiv
    """
    is_weekend = weekday >= 5

    if 5 <= hour < 9:
        predicted_change = +0.05 if not is_weekend else +0.02
        next_change_hours = 9 - hour
        reason = "Preise steigen morgens stark an"
    elif 9 <= hour < 12:
        predicted_change = -0.03
        next_change_hours = 12 - hour
        reason = "Preise fallen nach dem morgendlichen Hoch"
    elif 12 <= hour < 15:
        predicted_change = +0.02
        next_change_hours = 15 - hour
        reason = "Preise steigen mittags oft leicht an"
    elif 15 <= hour < 18:
        predicted_change = -0.04
        next_change_hours = 18 - hour
        reason = "Preise fallen am Nachmittag stetig"
    elif 18 <= hour < 21:
        predicted_change = -0.01
        next_change_hours = 21 - hour
        reason = "Jetzt ist statistisch der beste Zeitpunkt"
    elif 21 <= hour < 23:
        predicted_change = +0.06
        next_change_hours = 1
        reason = "Preise steigen nachts massiv an"
    else:
        predicted_change = 0
        next_change_hours = max(1, 5 - hour if hour < 5 else 29 - hour)
        reason = "Preise bleiben nachts auf hohem Niveau"

    # Trend einbeziehen
    if change_amount > 0.01:
        reason += " (aktuell steigend)"
        predicted_change += 0.01
    elif change_amount < -0.01:
        reason += " (aktuell fallend)"
        predicted_change -= 0.01

    reason += " [noch wenig Daten - Standardmuster]"

    predicted_price = round(current_price + predicted_change, 4)
    next_change_time = now + timedelta(hours=max(1, next_change_hours))

    return {
        "price": predicted_price,
        "change": predicted_change,
        "time": next_change_time,
        "reason": reason,
        "source": "statisch",
        "confidence": 20,
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
    """Formatiert den Preis als EUR-String mit 2 Dezimalstellen (deutsch)."""
    if price is None:
        return "---"
    truncated = int(price * 100) / 100
    return f"{truncated:.2f} EUR".replace(".", ",")


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


# ---------------------------------------------------------------------------
# Daten laden (v4 API)
# ---------------------------------------------------------------------------
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

        # Offene Stationen bevorzugen, geschlossene ans Ende
        stations.sort(key=lambda s: 0 if s.get("isOpen") else 1)

        result = stations[:MAX_STATIONS]

        # Preise in SQLite-Datenbank speichern
        now = datetime.now(BERLIN_TZ)
        for s in result:
            for f in s.get("fuels", []):
                if f.get("name", "").lower().startswith("super e5"):
                    _record_price_db(
                        s["id"],
                        s.get("brand") or s.get("name", "?"),
                        f.get("price"),
                        now
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
    ET.SubElement(channel, "title").text = (
        "Tankpreise E5 - Wennigsen (5km)"
    )
    ET.SubElement(channel, "link").text = (
        "https://creativecommons.tankerkoenig.de"
    )
    ET.SubElement(channel, "description").text = (
        "Die guenstigsten E5-Tankstellen im Umkreis von Wennigsen"
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
        for i, s in enumerate(stations, 1):
            # E5-Daten finden
            e5_fuel = None
            for f in s.get("fuels", []):
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
            name = s.get("name", "")
            street = s.get("street", "")
            place = s.get("place", "")
            dist = s.get("dist", 0)
            is_open = s.get("isOpen", False)
            status = "offen" if is_open else "geschlossen"

            # Trend-Pfeil
            if change_amount > 0:
                trend = "^"  # gestiegen
            elif change_amount < 0:
                trend = "v"  # gefallen
            else:
                trend = "="  # gleich

            # --- KI-PREISPROGNOSE ---
            prediction = _predict_price(s, e5_fuel)

            # Warnsignal falls Preis in < 15 Min steigt
            warning = ""
            if prediction and prediction["change"] > 0:
                time_diff = prediction["time"] - now
                if time_diff.total_seconds() <= 900:  # 15 Minuten
                    warning = "! "

            # --- TITEL ---
            # Format: "! 1,88\u20ac ^ | TAS (offen)"
            item = ET.SubElement(channel, "item")
            ET.SubElement(item, "title").text = (
                f"{warning}{_format_price(price)}\u20ac {trend} | {brand} ({status})"
            )

            # --- BESCHREIBUNG / DETAILS ---
            desc_parts = []

            # Adresse
            desc_parts.append(f"{name}")
            desc_parts.append(f"{street}, {place}")
            desc_parts.append(f"Entfernung: {dist:.1f} km")
            desc_parts.append("")

            # Preisdetails
            desc_parts.append(f"E5-Preis: {_format_price_eur(price)}")

            # Letzte Preisaenderung
            if change_ts:
                change_str = change_ts.strftime("%d.%m.%Y %H:%M")
                ago_str = _time_ago(change_ts)
                if change_amount > 0:
                    desc_parts.append(
                        f"Letzte Aenderung: +{abs(change_amount):.2f} EUR "
                        f"am {change_str} ({ago_str})"
                    )
                elif change_amount < 0:
                    desc_parts.append(
                        f"Letzte Aenderung: -{abs(change_amount):.2f} EUR "
                        f"am {change_str} ({ago_str})"
                    )
                else:
                    desc_parts.append(
                        f"Letzte Aenderung: am {change_str} ({ago_str})"
                    )

            # Alle Kraftstoffpreise
            desc_parts.append("")
            desc_parts.append("Alle Preise:")
            for f in s.get("fuels", []):
                f_name = f.get("name", "?")
                f_price = f.get("price")
                desc_parts.append(
                    f"  {f_name}: {_format_price_eur(f_price)}"
                )

            # Oeffnungszeiten
            closes_at = s.get("closesAt")
            if closes_at:
                close_dt = _parse_timestamp(closes_at)
                if close_dt:
                    desc_parts.append("")
                    desc_parts.append(
                        f"Schliesst um: {close_dt.strftime('%H:%M')} Uhr"
                    )

            # KI-Prognose-Details
            if prediction:
                desc_parts.append("")
                source = prediction.get("source", "?")
                confidence = prediction.get("confidence", 0)

                if source == "ki":
                    desc_parts.append(
                        f"--- KI-Prognose ({confidence}% sicher) ---"
                    )
                else:
                    desc_parts.append(
                        f"--- Prognose (Standardmuster) ---"
                    )

                pred_price = prediction["price"]
                pred_change = prediction["change"]
                pred_time = prediction["time"]
                pred_reason = prediction["reason"]

                if pred_change > 0:
                    direction = f"+{pred_change:.2f}"
                elif pred_change < 0:
                    direction = f"{pred_change:.2f}"
                else:
                    direction = "unveraendert"

                desc_parts.append(
                    f"Erwarteter Preis: ca. {_format_price_eur(pred_price)} "
                    f"({direction} EUR)"
                )
                desc_parts.append(
                    f"Voraussichtlich ab: "
                    f"ca. {pred_time.strftime('%H:%M')} Uhr"
                )
                desc_parts.append(f"Einschaetzung: {pred_reason}")

            ET.SubElement(item, "description").text = "\n".join(desc_parts)

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
        f"<p>Tankstellen: <b>{stats['stations']}</b></p>"
        f"<p>&Auml;ltester Eintrag: {stats['oldest'] or 'noch keine Daten'}</p>"
        f"<p>Neuester Eintrag: {stats['newest'] or 'noch keine Daten'}</p>"
        "<p><a href='/stats'>Detaillierte Statistiken</a></p>"
    )


@app.route("/feed.rss")
@app.route("/feed")
def rss_feed():
    xml = _build_feed()
    return Response(xml, mimetype="application/rss+xml")


@app.route("/health")
def health():
    """Health-Check (leichtgewichtig fuer Render.com)."""
    return {"status": "ok"}


@app.route("/stats")
def stats():
    """Zeigt KI-Statistiken und Datenbank-Infos."""
    db_stats = _get_db_stats()
    now = datetime.now(BERLIN_TZ)

    html = ["<h1>KI-Statistiken</h1>"]
    html.append(f"<p>Aktuelle Zeit: {now.strftime('%d.%m.%Y %H:%M')}</p>")
    html.append(f"<p>Datensaetze: {db_stats['total_records']}</p>")
    html.append(f"<p>Tankstellen: {db_stats['stations']}</p>")
    html.append(f"<p>Aeltester Eintrag: {db_stats['oldest'] or '-'}</p>")
    html.append(f"<p>Neuester Eintrag: {db_stats['newest'] or '-'}</p>")

    # Stunden-Profile der Stationen anzeigen
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

        profile = _get_hourly_profile(station_id, weekday=now.weekday())
        if not profile:
            profile = _get_hourly_profile(station_id)

        if profile:
            html.append("<table border='1' cellpadding='4'>")
            html.append("<tr><th>Stunde</th><th>Durchschnitt</th>"
                        "<th>Min</th><th>Max</th><th>Datenpunkte</th></tr>")
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
        else:
            html.append("<p><i>Noch keine historischen Daten vorhanden.</i></p>")

    return "\n".join(html)


# ---------------------------------------------------------------------------
# Datenbank beim Start initialisieren
# ---------------------------------------------------------------------------
_init_db()


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000)
