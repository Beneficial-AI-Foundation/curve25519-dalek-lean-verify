#!/bin/bash
# Comprehensive Lean benchmark with perf stats and per-file timing
# Usage: nice -n 19 ./scripts/bench/benchmark-full.sh
#
# Features:
#   - Per-file timing via lean wrapper (single build pass)
#   - Overall perf stats (instructions, task-clock, cache-misses) if available
#   - JSON summary output
#   - Results saved to benchmarks/<timestamp>/

set -eo pipefail
cd "$(dirname "$0")/../.."

TIMESTAMP=$(date +%Y%m%d-%H%M%S)
RESULTS_DIR="benchmarks/$TIMESTAMP"
mkdir -p "$RESULTS_DIR"

TIMELOG="$RESULTS_DIR/times.txt"
PERFLOG="$RESULTS_DIR/perf.txt"
SUMMARY="$RESULTS_DIR/summary.json"

WRAPPER_DIR=$(mktemp -d)
REAL_LEAN=$(which lean)

# Check if perf is available
HAS_PERF=false
if command -v perf &>/dev/null; then
    HAS_PERF=true
fi

# Create wrapper that logs timing
cat > "$WRAPPER_DIR/lean" << 'WRAPPER_EOF'
#!/bin/bash
REAL_LEAN="__REAL_LEAN__"
TIMELOG="__TIMELOG__"

START=$(date +%s%3N)
"$REAL_LEAN" "$@"
RET=$?
END=$(date +%s%3N)

# Log only .lean file compilations
for arg in "$@"; do
    if [[ "$arg" == *.lean ]]; then
        echo "$((END-START)) $arg" >> "$TIMELOG"
        break
    fi
done

exit $RET
WRAPPER_EOF

# Substitute paths into wrapper
sed -i "s|__REAL_LEAN__|$REAL_LEAN|g" "$WRAPPER_DIR/lean"
sed -i "s|__TIMELOG__|$TIMELOG|g" "$WRAPPER_DIR/lean"
chmod +x "$WRAPPER_DIR/lean"

echo "=== Comprehensive Lean Benchmark ==="
echo "Date: $(date)"
echo "Commit: $(git rev-parse --short HEAD 2>/dev/null || echo 'N/A')"
echo "Results: $RESULTS_DIR/"
echo ""

# Count project files
PROJECT_FILES=$(find . -name "*.lean" -not -path "./.lake/*" | wc -l)
echo "Project files: $PROJECT_FILES"
echo ""

# Clean build and restore mathlib cache
echo "Cleaning build..."
nice -n 19 lake clean >/dev/null 2>&1 || true

# Cache get function with proper exit code
cache_get() {
    nice -n 19 lake exe cache get 2>&1
    return $?
}

echo "Restoring mathlib cache (attempt 1)..."
if ! cache_get; then
    echo "Cache get failed, retrying (attempt 2)..."
    sleep 2
    if ! cache_get; then
        echo "ERROR: lake exe cache get failed twice. Aborting to avoid rebuilding mathlib."
        rm -rf "$WRAPPER_DIR"
        exit 1
    fi
fi
echo "Cache restored successfully."

# Run build with wrapper (and perf if available)
echo "Building with profiling wrapper..."
echo "(This takes ~1h, running with nice -n 19)"
echo ""

BUILD_START=$(date +%s)

if $HAS_PERF; then
    echo "Using perf stat for hardware counters..."
    nice -n 19 perf stat -o "$PERFLOG" -e task-clock,instructions,cache-misses,page-faults \
        env PATH="$WRAPPER_DIR:$PATH" lake build 2>&1 | tail -10
else
    echo "perf not available, using basic timing..."
    nice -n 19 env PATH="$WRAPPER_DIR:$PATH" lake build 2>&1 | tail -10
fi

BUILD_END=$(date +%s)
BUILD_TIME=$((BUILD_END - BUILD_START))

echo ""
echo "=== BUILD COMPLETE ==="
echo "Total build time: ${BUILD_TIME}s"
echo ""

# Show perf results if available
if $HAS_PERF && [ -f "$PERFLOG" ]; then
    echo "=== PERF STATS ==="
    cat "$PERFLOG"
    echo ""
fi

# Show top 20 slowest files
echo "=== TOP 20 SLOWEST FILES ==="
if [ -f "$TIMELOG" ]; then
    sort -rn "$TIMELOG" | head -20 | while read ms f; do
        TIME_S=$((ms / 1000)).$((ms % 1000 / 100))
        printf "%7ss  %s\n" "$TIME_S" "$f"
    done
else
    echo "No timing data collected"
fi

echo ""

# Generate JSON summary
cat > "$SUMMARY" << EOF
{
  "timestamp": "$TIMESTAMP",
  "commit": "$(git rev-parse --short HEAD 2>/dev/null || echo 'N/A')",
  "build_time_seconds": $BUILD_TIME,
  "project_files": $PROJECT_FILES,
  "has_perf": $HAS_PERF,
  "results_dir": "$RESULTS_DIR"
}
EOF

echo "=== RESULTS SAVED ==="
echo "  $TIMELOG - per-file timing (ms filepath)"
[ -f "$PERFLOG" ] && echo "  $PERFLOG - perf stat output"
echo "  $SUMMARY - JSON summary"
echo ""
echo "To profile a specific slow file:"
echo "  lake env lean --profile <file.lean>"

# Cleanup
rm -rf "$WRAPPER_DIR"

echo ""
echo "Done!"
