#!/usr/bin/env bash
set -u

interval=${TUZA_RESOURCE_LOG_INTERVAL_SECONDS:-60}
case "$interval" in
  ''|*[!0-9]*)
    echo "error: TUZA_RESOURCE_LOG_INTERVAL_SECONDS must be a positive integer" >&2
    exit 2
    ;;
esac
if [ "$interval" -eq 0 ]; then
  echo "error: TUZA_RESOURCE_LOG_INTERVAL_SECONDS must be positive" >&2
  exit 2
fi

while true; do
  echo "=== Tuza runner resources $(date --utc --iso-8601=seconds) ==="
  free -h
  df -h /
  ps -eo pid=,rss=,vsz=,etimes=,comm= --sort=-rss | head -n 8 || true
  sleep "$interval"
done
