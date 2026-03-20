#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: ./scripts/build-blueprint.sh [OUTPUT_ROOT]

Build the Curve25519-Dalek documentation blueprint artifacts.

Defaults:
  OUTPUT_ROOT = _out/blueprint

Artifacts:
  - curve25519docs (Curve25519-Dalek verification documentation)
EOF
}

case "${1:-}" in
  -h|--help)
    usage
    exit 0
    ;;
esac

if (( $# > 1 )); then
  usage >&2
  exit 1
fi

# Change to repo root
cd "$(dirname "$0")/.."

out_root="${1:-_out/blueprint}"
mkdir -p "$out_root"

echo "[build-blueprint] building curve25519docs executable"
lake build curve25519docs

echo "[build-blueprint] generating blueprint -> ${out_root}"
".lake/build/bin/curve25519docs" --output "$out_root"

echo "[build-blueprint] done"
echo "[build-blueprint] output:"
readlink -f "$out_root"
