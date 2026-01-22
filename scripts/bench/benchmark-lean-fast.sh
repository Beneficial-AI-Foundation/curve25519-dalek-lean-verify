#!/bin/bash
# Fast per-file Lean benchmark using lean wrapper during lake build
# Usage: ./scripts/bench/benchmark-lean-fast.sh
#
# This wraps the lean compiler to log timing for each file during a single
# lake build pass - much faster than running lake env lean per file.

set -eo pipefail
cd "$(dirname "$0")/../.."

TIMELOG=$(mktemp)
WRAPPER_DIR=$(mktemp -d)
REAL_LEAN=$(which lean)

# Create wrapper that logs timing
cat > "$WRAPPER_DIR/lean" << EOF
#!/bin/bash
START=\$(date +%s%3N)
"$REAL_LEAN" "\$@"
RET=\$?
END=\$(date +%s%3N)
# Log only .lean file compilations (skip other lean invocations)
for arg in "\$@"; do
    if [[ "\$arg" == *.lean ]]; then
        echo "\$((END-START)) \$arg" >> "$TIMELOG"
        break
    fi
done
exit \$RET
EOF
chmod +x "$WRAPPER_DIR/lean"

echo "=== Fast Lean Compilation Benchmark ==="
echo "Date: $(date)"
echo ""

# Clean and rebuild with wrapper
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
        rm -rf "$WRAPPER_DIR" "$TIMELOG"
        exit 1
    fi
fi
echo "Cache restored successfully."

echo "Building with timing wrapper (this takes ~1h)..."
PATH="$WRAPPER_DIR:$PATH" nice -n 19 lake build 2>&1 | tail -5

echo ""
echo "=== TOP 20 SLOWEST FILES ==="
sort -rn "$TIMELOG" | head -20 | while read ms f; do
    TIME_S=$((ms / 1000)).$((ms % 1000 / 100))
    printf "%6ss  %s\n" "$TIME_S" "$f"
done

# Save full results
RESULTS="benchmarks/benchmark-$(date +%Y%m%d-%H%M%S).txt"
mkdir -p benchmarks
sort -rn "$TIMELOG" > "$RESULTS"
echo ""
echo "Full results saved to: $RESULTS"

rm -rf "$WRAPPER_DIR" "$TIMELOG"
