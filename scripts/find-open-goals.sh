#!/bin/bash
#
# find-open-goals.sh - Find all open goals for a theorem
#
# Usage: ./find-open-goals.sh <theorem_id>
#
# Outputs: One goal ID per line for each open goal
# Exit codes:
#   0 - Found open goals (or none exist)
#   1 - Error

TID="${1:-}"

if [ -z "$TID" ]; then
    echo "Usage: $0 <theorem_id>" >&2
    exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
E="$SCRIPT_DIR/ensue-api.sh"

if [ ! -f "$E" ]; then
    echo "ERROR: ensue-api.sh not found" >&2
    exit 1
fi

# Get all goal status keys
RESULT=$("$E" list_keys "{\"prefix\":\"proofs/$TID/goals/\",\"limit\":100}" 2>/dev/null)

# Extract status keys
STATUS_KEYS=$(echo "$RESULT" | jq -r '.result.structuredContent.keys[].key_name' 2>/dev/null | grep '/status$')

if [ -z "$STATUS_KEYS" ]; then
    exit 0  # No goals
fi

# Build batch request for all statuses
KEY_ARRAY=$(echo "$STATUS_KEYS" | while read key; do echo "\"$key\""; done | tr '\n' ',' | sed 's/,$//')
STATUSES=$("$E" get_memory "{\"key_names\":[$KEY_ARRAY]}" 2>/dev/null)

# Find claimable goals (open, needs_verification, needs_decomposition)
echo "$STATUSES" | jq -r '
    .result.structuredContent.results[] |
    select(.value == "open" or .value == "needs_verification" or .value == "needs_decomposition") |
    .key_name |
    gsub("proofs/[^/]+/goals/"; "") |
    gsub("/status$"; "")
' 2>/dev/null
