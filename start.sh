#!/bin/sh
set -e

echo "[Start] Neuesten Code von GitHub holen..."
git clone --depth=1 https://github.com/bannanenbaer/tankpreise-rss-feed.git /tmp/repo
cp /tmp/repo/rss_server.py /app/rss_server.py
rm -rf /tmp/repo
echo "[Start] Code aktualisiert. Starte Gunicorn..."

exec gunicorn \
  --bind 0.0.0.0:5000 \
  --workers 2 \
  --timeout 60 \
  --max-requests 1000 \
  --max-requests-jitter 100 \
  rss_server:app
