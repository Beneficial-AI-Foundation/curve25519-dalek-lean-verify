#!/bin/bash
# Profile Lean files and save to JSON
# Usage:
#   ./scripts/bench/profile-lean.sh file.lean              # single file
#   ./scripts/bench/profile-lean.sh Folder/                # single folder
#   ./scripts/bench/profile-lean.sh Folder1/ Folder2/      # multiple folders
#   ./scripts/bench/profile-lean.sh --all                  # whole project

set -eo pipefail
cd "$(dirname "$0")/../.."

TIMESTAMP=$(date +%Y%m%d-%H%M%S)
OUTPUT_DIR="benchmarks/profile-$TIMESTAMP"
mkdir -p "$OUTPUT_DIR"

JSON_FILE="$OUTPUT_DIR/profile.json"
RAW_DIR="$OUTPUT_DIR/raw"
DETAILS_DIR="$OUTPUT_DIR/details"
mkdir -p "$RAW_DIR" "$DETAILS_DIR"

# Collect files to profile
FILES=()

if [ "$1" == "--all" ]; then
    echo "Profiling all project files..."
    while IFS= read -r f; do
        FILES+=("$f")
    done < <(find . -name "*.lean" -not -path "./.lake/*" | sort)
elif [ $# -eq 0 ]; then
    echo "Usage:"
    echo "  $0 file.lean              # single file"
    echo "  $0 Folder/                # single folder"
    echo "  $0 Folder1/ Folder2/      # multiple folders"
    echo "  $0 --all                  # whole project"
    exit 1
else
    for arg in "$@"; do
        if [ -f "$arg" ]; then
            FILES+=("$arg")
        elif [ -d "$arg" ]; then
            while IFS= read -r f; do
                FILES+=("$f")
            done < <(find "$arg" -name "*.lean" | sort)
        else
            echo "Warning: $arg not found, skipping"
        fi
    done
fi

COUNT=${#FILES[@]}
echo "=== Lean Profile ==="
echo "Date: $(date)"
echo "Files: $COUNT"
echo "Output: $OUTPUT_DIR/"
echo ""

# Check if project is built
if [ ! -d ".lake/build/lib/lean/Curve25519Dalek" ]; then
    echo "Project not built. Run 'nice -n 19 lake build' first."
    exit 1
fi

# Start JSON array
echo "[" > "$JSON_FILE"
FIRST=true

N=0
for f in "${FILES[@]}"; do
    N=$((N+1))

    SAFE_NAME=$(echo "$f" | tr '/' '_' | tr '.' '_')
    RAW_FILE="$RAW_DIR/${SAFE_NAME}.txt"
    DETAILS_FILE="$DETAILS_DIR/${SAFE_NAME}.jsonl"

    echo "[$N/$COUNT] Profiling $f ..."

    # Run lean --profile --json and capture output
    nice -n 19 lake env lean --profile --json "$f" > "$RAW_FILE" 2>&1 || true

    # Extract per-definition JSON lines (for detailed analysis)
    grep '^{' "$RAW_FILE" > "$DETAILS_FILE" 2>/dev/null || true

    # Parse cumulative times from end of output (POSIX-compatible, works on Linux/macOS/Windows)
    # Lean --profile outputs lines like "	simp 5.22s" or "	typeclass inference 340ms"
    # This awk block converts everything to seconds and emits shell variable assignments.
    IMPORT=0; SIMP=0; TYPECLASS=0; ELABORATION=0; TACTIC=0
    GRIND=0; INTERP=0; PARSING=0; TYPE_CHECK=0; INSTANTIATE=0
    eval "$(awk '
    /^\t/ {
        val = $NF
        # Convert to seconds: strip unit suffix
        if (val ~ /ms$/) { gsub(/ms$/, "", val); val = val / 1000 }
        else if (val ~ /s$/) { gsub(/s$/, "", val) }
        else { next }

        # Match metric name from the leading fields
        line = $0; sub(/^[\t ]+/, "", line); sub(/[ \t]+[^ \t]+$/, "", line)
        if (line == "import") printf "IMPORT=%s\n", val
        else if (line == "simp") printf "SIMP=%s\n", val
        else if (line == "typeclass inference") printf "TYPECLASS=%s\n", val
        else if (line == "elaboration") printf "ELABORATION=%s\n", val
        else if (line == "tactic execution") printf "TACTIC=%s\n", val
        else if (line == "grind") printf "GRIND=%s\n", val
        else if (line == "interpretation") printf "INTERP=%s\n", val
        else if (line == "parsing") printf "PARSING=%s\n", val
        else if (line == "type checking") printf "TYPE_CHECK=%s\n", val
        else if (line == "instantiate metavars") printf "INSTANTIATE=%s\n", val
    }' "$RAW_FILE")"

    # Write JSON entry
    if ! $FIRST; then echo "," >> "$JSON_FILE"; fi
    FIRST=false

    cat >> "$JSON_FILE" << EOF
  {
    "file": "$f",
    "import_s": ${IMPORT:-0},
    "simp_s": ${SIMP:-0},
    "typeclass_inference_s": ${TYPECLASS:-0},
    "elaboration_s": ${ELABORATION:-0},
    "tactic_execution_s": ${TACTIC:-0},
    "grind_s": ${GRIND:-0},
    "interpretation_s": ${INTERP:-0},
    "parsing_s": ${PARSING:-0},
    "type_checking_s": ${TYPE_CHECK:-0},
    "instantiate_metavars_s": ${INSTANTIATE:-0}
  }
EOF
done

# Close JSON array
echo "" >> "$JSON_FILE"
echo "]" >> "$JSON_FILE"

echo ""
echo "=== DONE ==="
echo "Output:"
echo "  Overview: $JSON_FILE"
echo "  Details:  $DETAILS_DIR/ (per-definition timing)"
echo "  Raw:      $RAW_DIR/"
echo ""
echo "View overview: ./scripts/bench/profile-report.sh $JSON_FILE"
echo "View details:  cat $DETAILS_DIR/<file>.jsonl | jq"
