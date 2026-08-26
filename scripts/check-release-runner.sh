#!/usr/bin/env bash
set -euo pipefail

minimum_memory_kib=$((48 * 1024 * 1024))
minimum_disk_kib=$((80 * 1024 * 1024))
memory_kib=$(awk '/^MemTotal:/ { print $2 }' /proc/meminfo)
disk_kib=$(df --output=avail -k . | tail -n 1 | tr -d '[:space:]')

free -h
df -h .

if [ "$memory_kib" -lt "$minimum_memory_kib" ]; then
  echo "error: full replay requires at least 48 GiB of physical memory" >&2
  exit 1
fi

if [ "$disk_kib" -lt "$minimum_disk_kib" ]; then
  echo "error: full replay requires at least 80 GiB of free workspace storage" >&2
  exit 1
fi

for command in cargo git python3; do
  if ! command -v "$command" >/dev/null 2>&1; then
    echo "error: release runner is missing required command: $command" >&2
    exit 1
  fi
done
