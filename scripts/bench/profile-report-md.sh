#!/bin/bash
# Generate Markdown profile report for GitHub Issues
# Usage:
#   ./scripts/bench/profile-report-md.sh <profile.json>
#   ./scripts/bench/profile-report-md.sh <profile.json> --heartbeats <file> --commit SHA --scope LABEL

set -e

if [ -z "$1" ] || [ ! -f "$1" ]; then
    echo "Usage: $0 <profile.json> [--heartbeats FILE] [--commit SHA] [--scope LABEL]" >&2
    exit 1
fi

JSON_FILE="$1"
shift

# Defaults
HEARTBEATS_FILE=""
COMMIT=""
SCOPE="specs+math"

# Parse args
while [[ $# -gt 0 ]]; do
    case $1 in
        --heartbeats) HEARTBEATS_FILE="$2"; shift 2 ;;
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
echo ""

# --- Totals ---
echo "## Totals"
echo ""
echo "| Metric | Time |"
echo "|--------|------|"

jq -r '
  def fmt: . * 100 | round / 100 | tostring + "s";
  def fmt_min: . as $t | if $t >= 60 then "\($t / 60 | floor)m \($t % 60 | floor)s" else $t | fmt end;
  "| Simp | \([.[].simp_s] | add | fmt_min) |",
  "| Typeclass inference | \([.[].typeclass_inference_s] | add | fmt_min) |",
  "| Elaboration | \([.[].elaboration_s] | add | fmt_min) |",
  "| Tactic execution | \([.[].tactic_execution_s] | add | fmt_min) |",
  "| Grind | \([.[].grind_s] | add | fmt_min) |",
  "| Import | \([.[].import_s] | add | fmt_min) |",
  "| Parsing | \([.[].parsing_s] | add | fmt_min) |",
  "| Type checking | \([.[].type_checking_s] | add | fmt_min) |",
  "| Instantiate metavars | \([.[].instantiate_metavars_s] | add | fmt_min) |",
  "| Interpretation | \([.[].interpretation_s] | add | fmt_min) |"
' "$JSON_FILE"

echo ""

# --- Helper function for top-N tables ---
generate_table() {
    local metric="$1"
    local label="$2"

    echo "## Top 20 by $label"
    echo ""
    echo "| # | File | Simp (s) | Typeclass (s) | Elaboration (s) | Tactic (s) |"
    echo "|---|------|----------|---------------|-----------------|------------|"

    jq -r --arg metric "$metric" '
      sort_by(-.[$metric]) | .[0:20] | to_entries[] |
      "| \(.key + 1) | `\(.value.file)` | \(.value.simp_s | . * 100 | round / 100) | \(.value.typeclass_inference_s | . * 100 | round / 100) | \(.value.elaboration_s | . * 100 | round / 100) | \(.value.tactic_execution_s | . * 100 | round / 100) |"
    ' "$JSON_FILE"

    echo ""
}

generate_table "simp_s" "Simp Time"
generate_table "typeclass_inference_s" "Typeclass Inference"
generate_table "elaboration_s" "Elaboration Time"

# --- Heartbeat Overrides ---
if [ -n "$HEARTBEATS_FILE" ] && [ -f "$HEARTBEATS_FILE" ]; then
    OVERRIDE_COUNT=$(grep -c 'set_option.*maxHeartbeats' "$HEARTBEATS_FILE" 2>/dev/null || grep -c ':' "$HEARTBEATS_FILE" 2>/dev/null || echo "?")
    echo "## Heartbeat Overrides"
    echo ""
    echo "<details>"
    echo "<summary>Files with maxHeartbeats overrides (click to expand)</summary>"
    echo ""
    echo '```'
    cat "$HEARTBEATS_FILE"
    echo '```'
    echo ""
    echo "</details>"
    echo ""
fi

# --- Footer ---
echo "---"
echo "*Generated automatically by CI profiling workflow.*"
