#!/bin/bash
# Display profile results in human-readable form
# Usage:
#   ./scripts/bench/profile-report.sh <profile.json>           # show top 20 by simp time
#   ./scripts/bench/profile-report.sh <profile.json> --top 10  # show top 10
#   ./scripts/bench/profile-report.sh <profile.json> --by typeclass_inference_s

set -e

if [ -z "$1" ] || [ ! -f "$1" ]; then
    echo "Usage: $0 <profile.json> [--top N] [--by METRIC]"
    echo ""
    echo "Metrics: simp_s, typeclass_inference_s, import_s, elaboration_s,"
    echo "         tactic_execution_s, grind_s, interpretation_s, parsing_s,"
    echo "         type_checking_s, instantiate_metavars_s"
    echo ""
    echo "Example:"
    echo "  $0 benchmarks/profile-20260121/profile.json --top 10 --by simp_s"
    exit 1
fi

JSON_FILE="$1"
shift

# Defaults
TOP=20
METRIC="simp_s"

# Parse args
while [[ $# -gt 0 ]]; do
    case $1 in
        --top) TOP="$2"; shift 2 ;;
        --by) METRIC="$2"; shift 2 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

echo "=== Profile Report ==="
echo "File: $JSON_FILE"
echo "Metric: $METRIC"
echo "Top: $TOP"
echo ""

# Check if jq is available
if ! command -v jq &>/dev/null; then
    echo "Error: jq is required. Install with: apt install jq"
    exit 1
fi

# Total stats
echo "=== TOTALS ==="
jq -r '
  "Files: \(length)",
  "Total simp: \([.[].simp_s] | add | . / 60 | floor)m \([.[].simp_s] | add | . % 60 | floor)s",
  "Total typeclass: \([.[].typeclass_inference_s] | add | . / 60 | floor)m \([.[].typeclass_inference_s] | add | . % 60 | floor)s",
  "Total import: \([.[].import_s] | add | . / 60 | floor)m \([.[].import_s] | add | . % 60 | floor)s",
  "Total grind: \([.[].grind_s] | add | . / 60 | floor)m \([.[].grind_s] | add | . % 60 | floor)s"
' "$JSON_FILE"

echo ""
echo "=== TOP $TOP BY $METRIC ==="
printf "%-10s %-10s %-10s %-10s %s\n" "SIMP" "TYPECLASS" "GRIND" "IMPORT" "FILE"
echo "--------------------------------------------------------------------------------"

jq -r --arg metric "$METRIC" --argjson top "$TOP" '
  sort_by(-.[$metric]) | .[:$top] | .[] |
  "\(.simp_s | tostring | .[0:8])s \(.typeclass_inference_s | tostring | .[0:8])s \(.grind_s | tostring | .[0:8])s \(.import_s | tostring | .[0:8])s \(.file)"
' "$JSON_FILE" | while read simp tc grind imp file; do
    printf "%-10s %-10s %-10s %-10s %s\n" "$simp" "$tc" "$grind" "$imp" "$file"
done

echo ""
echo "=== METRIC BREAKDOWN ==="
echo "Top consumers of $METRIC:"
jq -r --arg metric "$METRIC" --argjson top "$TOP" '
  sort_by(-.[$metric]) | .[:$top] | .[] |
  "  \(.[$metric])s  \(.file)"
' "$JSON_FILE"
