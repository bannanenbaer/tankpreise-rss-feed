from flask import Flask, Response
import requests
from datetime import datetime
import xml.etree.ElementTree as ET
from xml.dom import minidom

app = Flask(__name__)

LAT = 52.2762744
LNG = 9.5671846
RADIUS = 5
FUEL_TYPE = "e5"
MAX_STATIONS = 5
API_KEY = "00000000-0000-0000-0000-000000000002"
API_URL = "https://creativecommons.tankerkoenig.de/json/list.php"

def fetch_fuel_prices():
    params = {
        "lat": LAT, "lng": LNG, "rad": RADIUS,
        "sort": "price", "type": FUEL_TYPE, "apikey": API_KEY
    }
    try:
        response = requests.get(API_URL, params=params, timeout=10)
        data = response.json()
        if data.get("ok"):
            return data.get("stations", [])[:MAX_STATIONS]
    except:
        pass
    return []

def generate_rss_feed():
    stations = fetch_fuel_prices()
    rss = ET.Element("rss", version="2.0")
    channel = ET.SubElement(rss, "channel")
    title = ET.SubElement(channel, "title")
    title.text = "Tankpreise E5 - Wennigsen (5km)"
    link = ET.SubElement(channel, "link")
    link.text = "https://creativecommons.tankerkoenig.de"
    desc = ET.SubElement(channel, "description")
    desc.text = "Die guenstigsten E5-Tankstellen"
    lang = ET.SubElement(channel, "language")
    lang.text = "de-de"
    
    if not stations:
        item = ET.SubElement(channel, "item")
        t = ET.SubElement(item, "title")
        t.text = "Keine Daten verfuegbar"
    else:
        for i, s in enumerate(stations, 1):
            item = ET.SubElement(channel, "item")
            t = ET.SubElement(item, "title")
            price = s.get("price", 0)
            brand = s.get("brand") or s.get("name", "?")
            t.text = f"{i}. {price:.2f} EUR - {brand}"
            d = ET.SubElement(item, "description")
            name = s.get("name", "")
            street = s.get("street", "")
            place = s.get("place", "")
            dist = s.get("dist", 0)
            status = "OFFEN" if s.get("isOpen") else "GESCHLOSSEN"
            d.text = f"{name}\n{street}, {place}\n{dist:.1f} km - {status}"
    
    xml_str = ET.tostring(rss, encoding="unicode")
    dom = minidom.parseString(xml_str)
    return dom.toprettyxml(indent="  ", encoding="utf-8").decode("utf-8")

@app.route("/")
def index():
    return "<h1>Tankpreise RSS</h1><p><a href='/feed'>Zum Feed</a></p>"

@app.route("/feed.rss")
@app.route("/feed")
def rss_feed():
    return Response(generate_rss_feed(), mimetype="application/rss+xml")

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000)
