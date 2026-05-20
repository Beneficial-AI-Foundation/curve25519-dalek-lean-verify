#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: ./scripts/build-blueprint.sh [OUTPUT_ROOT]

Build the verso-blueprint documentation for the Lean verification project.

Defaults:
  OUTPUT_ROOT = _out/blueprint

Produces a static HTML site under OUTPUT_ROOT/html-multi/ that can be
served by any static-file webserver.
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

echo "[build-blueprint] building doc modules"
lake -d docs build Curve25519DalekDocs

echo "[build-blueprint] rendering HTML -> ${out_root}"
(cd docs && lake env lean --run Main.lean --output "../$out_root")

echo "[build-blueprint] done"
echo "[build-blueprint] output:"
readlink -f "$out_root"
echo ""
echo "To serve the documentation locally:"
echo "  python3 -m http.server 8080 -d $out_root/html-multi"
echo ""
echo "Then open http://localhost:8080 in your browser."
