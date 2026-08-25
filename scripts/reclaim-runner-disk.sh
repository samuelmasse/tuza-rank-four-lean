#!/usr/bin/env bash
set -euo pipefail

if [[ ${GITHUB_ACTIONS:-} != "true" || ${RUNNER_OS:-} != "Linux" ]]; then
  echo "error: runner-space cleanup is restricted to Linux GitHub Actions" >&2
  exit 1
fi

# The checked LRAT imports produce roughly 32 GiB of Lean build artifacts.
# Standard hosted runners carry unrelated SDK images that are not used here.
# Resolve every deletion target and accept only this fixed allowlist.
targets=(
  /usr/local/lib/android
  /usr/local/.ghcup
  /usr/share/dotnet
  /usr/share/swift
  /usr/share/miniconda
  /opt/ghc
  /usr/local/share/boost
  /usr/local/share/vcpkg
  /opt/hostedtoolcache
)

for target in "${targets[@]}"; do
  resolved=$(realpath -m -- "$target")
  case "$resolved" in
    /usr/local/lib/android|/usr/local/.ghcup|/usr/share/dotnet|/usr/share/swift|/usr/share/miniconda|/opt/ghc|/usr/local/share/boost|/usr/local/share/vcpkg|/opt/hostedtoolcache)
      ;;
    *)
      echo "error: refusing unexpected cleanup target $resolved" >&2
      exit 1
      ;;
  esac
  if [[ -e "$resolved" ]]; then
    sudo rm -rf --one-file-system -- "$resolved"
  fi
done

if command -v docker >/dev/null 2>&1; then
  sudo docker system prune --all --force --volumes
fi

sudo apt-get clean
df -h /
