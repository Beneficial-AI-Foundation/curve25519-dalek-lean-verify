#!/bin/bash
# Benchmark Lean proof build times with before/after comparison
#
# Usage:
#   ./scripts/bench/bench.sh baseline           # Record baseline timings
#   ./scripts/bench/bench.sh compare            # Compare current vs baseline
#   ./scripts/bench/bench.sh profile [files...]  # Profile specific files (no lakeprof needed)
#   ./scripts/bench/bench.sh status             # Show existing benchmarks
#
# Requires: lakeprof (for baseline/compare), jq (for reports)
# Install lakeprof:
#   uv tool install --from git+https://github.com/Kha/lakeprof lakeprof

set -eo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$PROJECT_DIR"

BENCH_DIR="benchmarks"

# --- Helpers ---

check_lakeprof() {
    if ! command -v lakeprof >/dev/null 2>&1; then
        echo "Error: lakeprof not found."
        echo ""
        echo "Install with:"
        echo "  uv tool install --from git+https://github.com/Kha/lakeprof lakeprof"
        exit 1
    fi
}

check_built() {
    if [ ! -d ".lake/build/lib" ]; then
        echo "Error: Project not built. Run 'lake build' first."
        exit 1
    fi
}

# Discover files with maxHeartbeats overrides (the likely slow files)
find_target_files() {
    git grep -l 'set_option.*maxHeartbeats' -- '*.lean' 2>/dev/null | sort
}

# Delete .olean/.ilean for given files to force rebuild
invalidate_oleans() {
    for f in "$@"; do
        local base="${f%.lean}"
        rm -f ".lake/build/lib/lean/${base}.olean" \
              ".lake/build/lib/lean/${base}.ilean" \
              ".lake/build/lib/lean/${base}.olean.hash" \
              ".lake/build/lib/lean/${base}.ilean.hash" \
              ".lake/build/lib/lean/${base}.trace"
    done
}

# Run profile-lean.sh on files and save results
run_profile() {
    local label="$1"
    shift
    local out_dir="$BENCH_DIR/$label-profile"
    rm -rf "$out_dir"

    # Temporarily override OUTPUT_DIR used by profile-lean.sh
    # We call it directly and move the output
    "$SCRIPT_DIR/profile-lean.sh" "$@"

    # Move latest profile output to our label directory
    local latest
    latest=$(ls -dt "$BENCH_DIR"/profile-* 2>/dev/null | head -1)
    if [ -n "$latest" ] && [ -d "$latest" ]; then
        mv "$latest" "$out_dir"
        echo "Profile saved to: $out_dir/"
    fi
}

# Print per-file comparison between two profile.json files
print_comparison() {
    local baseline_json="$1"
    local current_json="$2"

    if ! command -v jq >/dev/null 2>&1; then
        echo "(jq not found, skipping detailed comparison)"
        return
    fi

    echo ""
    echo "=== Per-File Comparison (baseline vs current) ==="
    printf "%-8s %-8s %-8s  %s\n" "BEFORE" "AFTER" "DELTA" "FILE"
    echo "----------------------------------------------"

    # Merge the two JSON arrays and compare by file
    jq -r -s '
        (.[0] | map({(.file): .}) | add) as $base |
        (.[1] | map({(.file): .}) | add) as $curr |
        ($curr | keys[]) as $f |
        ($base[$f] // {simp_s:0,typeclass_inference_s:0,elaboration_s:0,tactic_execution_s:0,grind_s:0}) as $b |
        ($curr[$f]) as $c |
        (($b.simp_s + $b.typeclass_inference_s + $b.elaboration_s + $b.tactic_execution_s + $b.grind_s) * 10 | round / 10) as $bt |
        (($c.simp_s + $c.typeclass_inference_s + $c.elaboration_s + $c.tactic_execution_s + $c.grind_s) * 10 | round / 10) as $ct |
        (($ct - $bt) * 10 | round / 10) as $delta |
        "\($bt)s\t\($ct)s\t\(if $delta > 0 then "+\($delta)s" else "\($delta)s" end)\t\($f)"
    ' "$baseline_json" "$current_json" | sort -t$'\t' -k3 -rn | while IFS=$'\t' read -r before after delta file; do
        printf "%-8s %-8s %-8s  %s\n" "$before" "$after" "$delta" "$file"
    done
}

# --- Commands ---

cmd_baseline() {
    check_lakeprof
    check_built
    mkdir -p "$BENCH_DIR"

    local files
    files=()
    while IFS= read -r f; do files+=("$f"); done < <(find_target_files)
    echo "=== Recording Baseline ==="
    echo "Target files: ${#files[@]} (with maxHeartbeats overrides)"
    echo ""

    # Invalidate and rebuild with lakeprof
    invalidate_oleans "${files[@]}"
    echo "--- lakeprof record ---"
    lakeprof record -o "$BENCH_DIR/baseline.log" lake build
    echo ""
    echo "--- lakeprof critical path ---"
    lakeprof report -i "$BENCH_DIR/baseline.log" -p
    echo ""

    # Per-file profiling
    echo "--- Per-file profiling ---"
    run_profile baseline "${files[@]}"

    echo ""
    echo "=== Baseline recorded ==="
    echo "Next: make changes, then run: $0 compare"
}

cmd_compare() {
    check_lakeprof
    check_built

    if [ ! -f "$BENCH_DIR/baseline.log" ]; then
        echo "Error: No baseline found. Run '$0 baseline' first."
        exit 1
    fi

    local files
    files=()
    while IFS= read -r f; do files+=("$f"); done < <(find_target_files)
    echo "=== Recording Current ==="
    echo "Target files: ${#files[@]}"
    echo ""

    # Invalidate and rebuild with lakeprof
    invalidate_oleans "${files[@]}"
    echo "--- lakeprof record ---"
    lakeprof record -o "$BENCH_DIR/current.log" lake build
    echo ""

    echo "--- lakeprof diff ---"
    lakeprof diff "$BENCH_DIR/baseline.log" "$BENCH_DIR/current.log"
    echo ""

    # Per-file profiling
    echo "--- Per-file profiling ---"
    run_profile current "${files[@]}"

    # Side-by-side comparison
    local baseline_json="$BENCH_DIR/baseline-profile/profile.json"
    local current_json="$BENCH_DIR/current-profile/profile.json"
    if [ -f "$baseline_json" ] && [ -f "$current_json" ]; then
        print_comparison "$baseline_json" "$current_json"
    fi
}

cmd_profile() {
    check_built
    mkdir -p "$BENCH_DIR"

    local files=("$@")
    if [ ${#files[@]} -eq 0 ]; then
        # Default: all files with maxHeartbeats overrides
        files=()
    while IFS= read -r f; do files+=("$f"); done < <(find_target_files)
    fi

    echo "=== Profiling ${#files[@]} files ==="
    echo ""
    run_profile "latest" "${files[@]}"

    # Print sorted summary
    local json="$BENCH_DIR/latest-profile/profile.json"
    if [ -f "$json" ] && command -v jq >/dev/null 2>&1; then
        echo ""
        echo "=== Results (sorted by total time, excluding imports) ==="
        printf "%-8s %-7s %-7s %-7s %-7s %-7s  %s\n" "TOTAL" "SIMP" "TACTIC" "ELAB" "GRIND" "TC" "FILE"
        echo "--------------------------------------------------------------------------------"
        jq -r '.[] |
            ((.simp_s + .tactic_execution_s + .elaboration_s + .grind_s + .typeclass_inference_s) * 10 | round / 10) as $total |
            "\($total)\t\(.simp_s)\t\(.tactic_execution_s)\t\(.elaboration_s)\t\(.grind_s)\t\(.typeclass_inference_s)\t\(.file)"
        ' "$json" | sort -t$'\t' -k1 -rn | while IFS=$'\t' read -r total simp tac elab grind tc file; do
            printf "%-8s %-7s %-7s %-7s %-7s %-7s  %s\n" "${total}s" "${simp}s" "${tac}s" "${elab}s" "${grind}s" "${tc}s" "$file"
        done
    fi
}

cmd_status() {
    echo "=== Benchmark Status ==="
    echo "Directory: $BENCH_DIR/"
    echo ""
    if [ -d "$BENCH_DIR" ]; then
        if [ -f "$BENCH_DIR/baseline.log" ]; then
            echo "Baseline: $(ls -lh "$BENCH_DIR/baseline.log" | awk '{print $5, $6, $7, $8}')"
        else
            echo "Baseline: (none)"
        fi
        if [ -f "$BENCH_DIR/current.log" ]; then
            echo "Current:  $(ls -lh "$BENCH_DIR/current.log" | awk '{print $5, $6, $7, $8}')"
        else
            echo "Current:  (none)"
        fi
        if [ -d "$BENCH_DIR/latest-profile" ]; then
            local count
            count=$(jq 'length' "$BENCH_DIR/latest-profile/profile.json" 2>/dev/null || echo "?")
            echo "Profile:  $count files in latest-profile/"
        fi
    else
        echo "(no benchmarks directory)"
    fi
}

# --- Main ---

case "${1:-}" in
    baseline) cmd_baseline ;;
    compare)  cmd_compare ;;
    profile)  shift; cmd_profile "$@" ;;
    status)   cmd_status ;;
    *)
        echo "Usage: $0 {baseline|compare|profile|status}"
        echo ""
        echo "Commands:"
        echo "  baseline           Record baseline timings (requires lakeprof)"
        echo "  compare            Compare current vs baseline (requires lakeprof)"
        echo "  profile [files..]  Profile files (defaults to all with maxHeartbeats overrides)"
        echo "  status             Show existing benchmark state"
        echo ""
        echo "Workflow:"
        echo "  1. $0 baseline     # before changes"
        echo "  2. # ... refactor proofs ..."
        echo "  3. $0 compare      # after changes"
        ;;
esac
