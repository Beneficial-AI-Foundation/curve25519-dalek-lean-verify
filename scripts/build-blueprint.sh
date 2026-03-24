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
out_root_abs="$(readlink -f "$out_root")"

echo "[build-blueprint] building docs executable"
cd docs
lake build docs

echo "[build-blueprint] generating blueprint -> ${out_root_abs}"
".lake/build/bin/docs" --output "$out_root_abs"

echo "[build-blueprint] done"
echo "[build-blueprint] output:"
echo "$out_root_abs"
echo ""
echo "To view the documentation, run:"
echo "  python3 -m http.server 8080 -d ${out_root_abs}/html-multi"
echo ""
echo "Then open http://localhost:8080 in your browser."
