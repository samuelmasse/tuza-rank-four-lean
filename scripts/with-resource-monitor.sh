#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
bash "$script_dir/monitor-runner-resources.sh" &
monitor_pid=$!
trap 'kill "$monitor_pid" 2>/dev/null || true' EXIT

"$@"
