"""
RSS-Feed für Tankpreise im Umkreis von Wennigsen (Deister).

Nutzt die Tankerkönig API v4 für:
- Korrekte Preisanzeige mit 2 Dezimalstellen im deutschen Format (z.B. 1,97)
- Zeitstempel der letzten Preisänderung
- Preisänderungsbetrag und Trend
- Preisprognose basierend auf typischen Tagesmustern

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

# ---------------------------------------------------------------------------
# Preishistorie für Prognose (im Speicher, pro Station)
# ---------------------------------------------------------------------------
# Format: { station_id: [(timestamp, price), ...] }
_price_history = {}
MAX_HISTORY = 50  # Max. Einträge pro Station


def _record_price(station_id, price, timestamp):
    """Speichert einen Preis in der Historie für Prognosen."""
    if station_id not in _price_history:
        _price_history[station_id] = []
    history = _price_history[station_id]
    # Nur speichern wenn sich der Preis geändert hat
    if not history or history[-1][1] != price:
        history.append((timestamp, price))
        # Alte Einträge entfernen
        if len(history) > MAX_HISTORY:
            _price_history[station_id] = history[-MAX_HISTORY:]


# ---------------------------------------------------------------------------
# Preisprognose
# ---------------------------------------------------------------------------
def _predict_price(station, fuel_data):
    """
    Erstellt eine einfache Preisprognose basierend auf:
    1. Typischen Tagesmuster (Preise fallen abends, steigen morgens)
    2. Letzter Preisänderung (Trend)
    3. Volatilität der Station
    """
    now = datetime.now(BERLIN_TZ)
    hour = now.hour
    last_change = fuel_data.get("lastChange", {})
    change_amount = last_change.get("amount", 0) or 0
    volatility = station.get("volatility", 0) or 0
    current_price = fuel_data.get("price", 0)

    if not current_price:
        return None, None

    # Typische Tankstellen-Preismuster in Deutschland:
    # - Preise steigen zwischen 5:00-8:00 Uhr (Berufsverkehr)
    # - Preise fallen gegen 10:00-12:00 Uhr
    # - Preise steigen gegen 13:00-15:00 Uhr
    # - Preise fallen gegen 18:00-20:00 Uhr (bester Zeitpunkt!)
    # - Preise steigen wieder ab 21:00-22:00 Uhr

    is_weekend = now.weekday() >= 5
    
    if 5 <= hour < 9:
        # Morgens: Preise steigen massiv (Berufsverkehr)
        predicted_change = +0.05 if not is_weekend else +0.02
        next_change_hours = 9 - hour
        reason = "Preise steigen morgens stark an"
    elif 9 <= hour < 12:
        # Vormittag: Erste Entspannung
        predicted_change = -0.03
        next_change_hours = 12 - hour
        reason = "Preise fallen nach dem morgendlichen Hoch"
    elif 12 <= hour < 15:
        # Mittag: Kleiner Peak
        predicted_change = +0.02
        next_change_hours = 15 - hour
        reason = "Preise steigen mittags oft leicht an"
    elif 15 <= hour < 18:
        # Nachmittag: Kontinuierlicher Abfall
        predicted_change = -0.04
        next_change_hours = 18 - hour
        reason = "Preise fallen am Nachmittag stetig"
    elif 18 <= hour < 21:
        # Abend: Tiefpunkt des Tages (Bester Zeitpunkt!)
        predicted_change = -0.01
        next_change_hours = 21 - hour
        reason = "Jetzt ist statistisch der beste Zeitpunkt!"
    elif 21 <= hour < 23:
        # Spaetabend: Preise ziehen wieder an
        predicted_change = +0.06
        next_change_hours = 1
        reason = "Preise steigen nachts massiv an"
    else:
        # Nacht: Hohes Niveau
        predicted_change = 0
        next_change_hours = max(1, 5 - hour if hour < 5 else 29 - hour)
        reason = "Preise bleiben nachts auf hohem Niveau"

    # Trend der letzten Änderung einbeziehen
    if change_amount > 0.01:
        reason += " (Trend: stark steigend)"
        predicted_change += 0.01
    elif change_amount < -0.01:
        reason += " (Trend: stark fallend)"
        predicted_change -= 0.01
    elif change_amount > 0:
        reason += " (Trend: leicht steigend)"
    elif change_amount < 0:
        reason += " (Trend: leicht fallend)"

    predicted_price = round(current_price + predicted_change, 3)
    next_change_time = now + timedelta(hours=next_change_hours)

    return {
        "price": predicted_price,
        "change": predicted_change,
        "time": next_change_time,
        "reason": reason,
    }, None


# ---------------------------------------------------------------------------
# Hilfsfunktionen
# ---------------------------------------------------------------------------
def _format_price(price):
    """Formatiert den Preis mit 2 Dezimalstellen im deutschen Format.
    Die letzte Ziffer (immer 9) wird abgeschnitten.
    z.B. 1.889 -> '1,88', 1.909 -> '1,90'"""
    if price is None:
        return "---"
    # Letzte Ziffer abschneiden: 1.889 -> 1.88
    truncated = int(price * 100) / 100
    return f"{truncated:.2f}".replace(".", ",")


def _format_price_eur(price):
    """Formatiert den Preis als EUR-String mit 2 Dezimalstellen (deutsch)."""
    if price is None:
        return "---"
    truncated = int(price * 100) / 100
    return f"{truncated:.2f} EUR".replace(".", ",")


def _parse_timestamp(ts_str):
    """Parst einen Tankerkönig-Zeitstempel -> datetime in Europe/Berlin."""
    if not ts_str:
        return None
    try:
        # Format: "2026-03-06T10:15:28+01" (manchmal ohne Minuten im Offset)
        # Normalisiere auf ISO-Format
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
    """Gibt eine lesbare Zeitdifferenz zurück (z.B. 'vor 15 Min')."""
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
    """Lädt Tankstellen und Preise von der Tankerkönig v4 API."""
    cached = _cache.get("stations")
    if cached is not None:
        return cached

    try:
        # Session mit Retries fuer mehr Zuverlaessigkeit
        session = requests.Session()
        retries = Retry(total=3, backoff_factor=0.5, status_forcelist=[500, 502, 503, 504])
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

        # Nach E5-Preis sortieren (günstigste zuerst)
        def _get_e5_price(station):
            for f in station.get("fuels", []):
                if f.get("name", "").lower().startswith("super e5"):
                    return f.get("price", 9999)
            return 9999

        stations.sort(key=_get_e5_price)

        # Nur offene Stationen bevorzugen, geschlossene ans Ende
        stations.sort(key=lambda s: 0 if s.get("isOpen") else 1)

        result = stations[:MAX_STATIONS]

        # Preise in Historie aufnehmen
        now = datetime.now(BERLIN_TZ)
        for s in result:
            for f in s.get("fuels", []):
                if f.get("name", "").lower().startswith("super e5"):
                    _record_price(s["id"], f.get("price"), now)

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
            "Die Tankerkoenig-API liefert derzeit keine Daten. "
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

            # --- TITEL ---
            # Format: "1,88€ v | TAS (offen)"
            item = ET.SubElement(channel, "item")
            ET.SubElement(item, "title").text = (
                f"{_format_price(price)}€ {trend} | {brand} ({status})"
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

            # Preisprognose
            prediction, _ = _predict_price(s, e5_fuel)
            if prediction:
                desc_parts.append("")
                desc_parts.append("--- Preisprognose ---")
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
    return (
        "<h1>Tankpreise RSS - Wennigsen</h1>"
        "<p><a href='/feed.rss'>Zum RSS-Feed</a></p>"
        "<p>Datenquelle: Tankerk&ouml;nig API v4 "
        "(CC BY 4.0)</p>"
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


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000)
