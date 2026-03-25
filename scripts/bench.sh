#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 2 ]]; then
    echo "Usage: $0 <library-name> <api-endpoint-base>" >&2
    echo "  e.g. $0 CurveDalek https://bench.example.com" >&2
    exit 1
fi

if [[ -z "${BENCH_AUTH_TOKEN:-}" ]]; then
    echo "Error: BENCH_AUTH_TOKEN environment variable is not set." >&2
    exit 1
fi

LIB_NAME="$1"
API_BASE="$2"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BENCH_DIR="$REPO_ROOT/bench_results"

# =============================================================================
# Setup
# =============================================================================
echo "--- Setup ---"

if ! command -v lakeprof &>/dev/null; then
    echo "Error: lakeprof is not installed or not on PATH." >&2
    echo "Install it from https://github.com/Kha/lakeprof" >&2
    exit 1
fi

if ! command -v lake &>/dev/null; then
    echo "Error: lake is not installed or not on PATH." >&2
    echo "Ensure elan is installed and a lean-toolchain is configured." >&2
    exit 1
fi

mkdir -p "$BENCH_DIR"

# =============================================================================
# Preprocess
#
# This section should be pre-populated by the user of the benchmarking tool with
# all pre-processing steps unique to the library being benchmarked.
#
# Examples of steps that might go here:
#   - lake exe cache get
#   - lake build Aeneas
#   - lake build PrimeCert
#   - Any other dependency builds you don't want included in benchmark timing
# =============================================================================
echo "--- Preprocess ---"
lake clean && lake exe cache get
lake build PrimeCert
lake build Aeneas

# =============================================================================
# Build
# =============================================================================
echo "--- Build ---"

lakeprof record lake build

lakeprof report -c

if [[ -f "lakeprof.log" ]]; then
    mv lakeprof.log "$BENCH_DIR/lakeprof.log"
else
    echo "Warning: lakeprof.log not found after report generation." >&2
fi

if [[ -f "lakeprof.trace_event" ]]; then
    mv lakeprof.trace_event "$BENCH_DIR/lakeprof.trace_event"
else
    echo "Warning: lakeprof.trace_event not found after report generation." >&2
fi

# =============================================================================
# Profile
# =============================================================================
echo "--- Profile ---"

LIB_DIR="$REPO_ROOT/$LIB_NAME"
PROFILE_DIR="$BENCH_DIR/profiles"

if [[ ! -d "$LIB_DIR" ]]; then
    echo "Error: Library directory not found: $LIB_DIR" >&2
    exit 1
fi

mkdir -p "$PROFILE_DIR"

find "$LIB_DIR" -name '*.lean' -type f | while read -r lean_file; do
    rel_path="${lean_file#"$REPO_ROOT/"}"
    out_name="${rel_path//\//__}"
    out_name="${out_name%.lean}.profile"

    echo "  Profiling: $rel_path"
    lake env lean -Dtrace.profiler=true "$lean_file" > "$PROFILE_DIR/$out_name" 2>&1 || true
done

ROOT_LEAN="$REPO_ROOT/$LIB_NAME.lean"
if [ -f "$ROOT_LEAN" ]; then
    echo "  Profiling: $LIB_NAME.lean"
    lake env lean -Dtrace.profiler=true "$ROOT_LEAN" > "$PROFILE_DIR/$LIB_NAME.profile" 2>&1 || true
fi

# =============================================================================
# Report
# =============================================================================
echo "--- Report ---"

REPO_NAME=$(gh repo view --json nameWithOwner -q .nameWithOwner)
COMMIT_HASH=$(git -C "$REPO_ROOT" rev-parse HEAD)
ARCHIVE="$REPO_ROOT/bench_results.tar.gz"

tar -czf "$ARCHIVE" -C "$REPO_ROOT" bench_results

echo "Uploading to $API_BASE/$REPO_NAME/$COMMIT_HASH ..."
curl -f -X POST \
    "${API_BASE}/${REPO_NAME}/${COMMIT_HASH}" \
    -H "Content-Type: application/gzip" \
    -H "Authorization: Bearer ${BENCH_AUTH_TOKEN}" \
    --data-binary "@$ARCHIVE"

rm -f "$ARCHIVE"

echo "===== Benchmark run complete ====="
