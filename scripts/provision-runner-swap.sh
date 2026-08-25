#!/usr/bin/env bash
set -euo pipefail

if [ "${GITHUB_ACTIONS:-}" != "true" ] || [ "${RUNNER_OS:-}" != "Linux" ]; then
  echo "error: bounded swap provisioning is restricted to ephemeral Linux GitHub Actions runners" >&2
  exit 2
fi

swap_path=/mnt/tuza-rank-four-ci.swap
swap_bytes=$((4 * 1024 * 1024 * 1024))
reserve_bytes=$((8 * 1024 * 1024 * 1024))

if [ -e "$swap_path" ]; then
  echo "error: refusing to replace existing path $swap_path" >&2
  exit 2
fi

available_bytes=$(df --output=avail -B1 /mnt | tail -n 1 | tr -d '[:space:]')
if [ "$available_bytes" -lt $((swap_bytes + reserve_bytes)) ]; then
  echo "error: insufficient runner disk for bounded swap and reserve" >&2
  echo "available=$available_bytes required=$((swap_bytes + reserve_bytes))" >&2
  exit 2
fi

sudo fallocate -l "$swap_bytes" "$swap_path"
sudo chmod 600 "$swap_path"
sudo mkswap "$swap_path"
sudo swapon "$swap_path"

echo "Provisioned 4 GiB of bounded swap at $swap_path"
free -h
df -h /
