FROM python:3.12-slim

WORKDIR /app

# Abhängigkeiten installieren
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# App-Code kopieren
COPY rss_server.py .

# Persistentes Verzeichnis für SQLite-Datenbank
RUN mkdir -p /data
VOLUME ["/data"]

# Port freigeben
EXPOSE 5000

# Gunicorn starten
CMD ["gunicorn", "--bind", "0.0.0.0:5000", "--workers", "2", "--timeout", "60", "rss_server:app"]
