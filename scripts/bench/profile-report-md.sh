#!/bin/bash
# Generate Markdown profile report for GitHub Issues
# Usage:
#   ./scripts/bench/profile-report-md.sh <profile.json>
#   ./scripts/bench/profile-report-md.sh <profile.json> --commit SHA --scope LABEL

set -e

if [ -z "$1" ] || [ ! -f "$1" ]; then
    echo "Usage: $0 <profile.json> [--commit SHA] [--scope LABEL]" >&2
    exit 1
fi

JSON_FILE="$1"
shift

# Defaults
COMMIT=""
SCOPE="specs+math"

# Parse args
while [[ $# -gt 0 ]]; do
    case $1 in
        --commit) COMMIT="$2"; shift 2 ;;
        --scope) SCOPE="$2"; shift 2 ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

# Check jq
if ! command -v jq &>/dev/null; then
    echo "Error: jq is required. Install with: apt install jq" >&2
    exit 1
fi

FILE_COUNT=$(jq 'length' "$JSON_FILE")
DATE=$(date +%Y-%m-%d)

# Compute total elaboration time
TOTAL_ELAB=$(jq -r '[.[].elaboration_s] | add | . * 100 | round / 100' "$JSON_FILE")

# --- Header ---
echo "# Lean Profiling Report"
echo ""
echo "| | |"
echo "|---|---|"
echo "| **Date** | $DATE |"
if [ -n "$COMMIT" ]; then
    SHORT_SHA="${COMMIT:0:7}"
    echo "| **Commit** | \`$SHORT_SHA\` |"
fi
echo "| **Scope** | $SCOPE |"
echo "| **Files profiled** | $FILE_COUNT |"
echo "| **Total elaboration** | ${TOTAL_ELAB}s |"
echo ""

# --- Per-file table sorted by elaboration time (slowest first) ---
echo "## Top 20 Slowest Files"
echo ""
echo "| # | File | Elaboration (s) |"
echo "|---|------|-----------------|"

jq -r '
  sort_by(-.elaboration_s) | .[0:20] | to_entries[] |
  "| \(.key + 1) | `\(.value.file)` | \(.value.elaboration_s | . * 100 | round / 100) |"
' "$JSON_FILE"

echo ""

# --- Footer ---
echo "---"
echo "*Generated automatically by CI profiling workflow.*"
