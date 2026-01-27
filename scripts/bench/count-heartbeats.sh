#!/bin/bash
# Count maxHeartbeats overrides - a proxy for elaboration complexity/tech debt
# Usage: ./scripts/bench/count-heartbeats.sh

cd "$(dirname "$0")/../.."

echo "=== Heartbeat Analysis ==="
echo ""

# Find all files with heartbeat overrides, sorted by value
echo "Files with maxHeartbeats overrides (sorted by value):"
echo ""

git grep -n 'set_option.*maxHeartbeats' -- '*.lean' 2>/dev/null | \
    sed 's/.*maxHeartbeats[[:space:]]*\([0-9]*\).*/\1 &/' | \
    sort -rn | \
    while read val line; do
        # Format large numbers
        if [ "$val" -ge 1000000000000 ]; then
            human="$((val / 1000000000000))T"
        elif [ "$val" -ge 1000000000 ]; then
            human="$((val / 1000000000))B"
        elif [ "$val" -ge 1000000 ]; then
            human="$((val / 1000000))M"
        elif [ "$val" -ge 1000 ]; then
            human="$((val / 1000))K"
        else
            human=$val
        fi
        printf "%10s  %s\n" "$human" "$(echo "$line" | cut -d' ' -f2-)"
    done

echo ""
TOTAL=$(git grep -c 'set_option.*maxHeartbeats' -- '*.lean' 2>/dev/null | awk -F: '{sum+=$2} END {print sum+0}')
echo "Total overrides: $TOTAL"
echo ""
echo "Note: Default maxHeartbeats is 200000. Higher values indicate complex elaboration."
