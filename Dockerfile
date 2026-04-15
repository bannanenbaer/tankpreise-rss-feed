FROM python:3.12-slim

# Git installieren
RUN apt-get update && apt-get install -y git && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# Abhängigkeiten vorab installieren (werden gecacht, nur neu gebaut wenn requirements.txt sich ändert)
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Persistentes Verzeichnis für SQLite-Datenbank
RUN mkdir -p /data
VOLUME ["/data"]

# Startskript: zieht beim Start immer den neuesten Code von GitHub
COPY start.sh .
RUN chmod +x start.sh

EXPOSE 5000

CMD ["/app/start.sh"]
