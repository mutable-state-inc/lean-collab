#!/bin/bash
#
# pre-verify.sh - MANDATORY check before attempting any tactic
#
# Usage: ./pre-verify.sh <theorem_id> <goal_id> <goal_type>
#
# This script:
# 1. Checks existing failed attempts (avoids redundant work)
# 2. Queries collective intelligence for relevant tactics
# 3. Returns suggestions to try
#
# Exit codes:
#   0 - Proceed with verification (prints suggested tactics)
#   1 - Error
#   2 - Too many failures recorded, skip this goal

set -e

THEOREM_ID="$1"
GOAL_ID="$2"
GOAL_TYPE="$3"

if [ -z "$THEOREM_ID" ] || [ -z "$GOAL_ID" ] || [ -z "$GOAL_TYPE" ]; then
    echo "Usage: $0 <theorem_id> <goal_id> <goal_type>" >&2
    exit 1
fi

# Find Ensue API (local)
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ENSUE="$SCRIPT_DIR/ensue-api.sh"
if [ ! -f "$ENSUE" ]; then
    echo "ERROR: ensue-api.sh not found at $ENSUE" >&2
    exit 1
fi

echo "=== PRE-VERIFY CHECK ===" >&2
echo "Theorem: $THEOREM_ID" >&2
echo "Goal: $GOAL_ID" >&2
echo "Type: $GOAL_TYPE" >&2

# Step 1: Check existing failed attempts
echo "" >&2
echo "--- Checking existing attempts ---" >&2

ATTEMPTS=$($ENSUE list_keys "{\"prefix\":\"proofs/$THEOREM_ID/goals/$GOAL_ID/attempts/\",\"limit\":20}" 2>/dev/null)
ATTEMPT_COUNT=$(echo "$ATTEMPTS" | grep -o '"count":[0-9]*' | grep -o '[0-9]*' || echo "0")

if [ "$ATTEMPT_COUNT" -gt 0 ]; then
    echo "Found $ATTEMPT_COUNT previous attempts:" >&2

    # Extract and show attempt details
    KEYS=$(echo "$ATTEMPTS" | grep -o '"key_name":"[^"]*"' | sed 's/"key_name":"//;s/"//' | head -5)
    if [ -n "$KEYS" ]; then
        KEY_ARRAY=$(echo "$KEYS" | tr '\n' ',' | sed 's/,$//')
        ATTEMPT_DATA=$($ENSUE get_memory "{\"key_names\":[$(echo "$KEY_ARRAY" | sed 's/\([^,]*\)/"\1"/g')]}" 2>/dev/null)

        # Parse and display failed tactics
        echo "$ATTEMPT_DATA" | grep -o '"tactic":"[^"]*"' | sed 's/"tactic":"//;s/"$//' | while read -r tactic; do
            echo "  - FAILED: $tactic" >&2
        done
    fi

    if [ "$ATTEMPT_COUNT" -ge 5 ]; then
        echo "" >&2
        echo "⚠️  WARNING: 5+ attempts already recorded. Consider decomposing instead." >&2
        exit 2
    fi
else
    echo "No previous attempts found." >&2
fi

# Step 2: Query collective intelligence
echo "" >&2
echo "--- Querying collective intelligence ---" >&2

# Build query from goal type (extract key terms)
QUERY=$(echo "$GOAL_TYPE" | sed 's/[^A-Za-z0-9 ]/ /g' | tr -s ' ' | cut -c1-100)

# Search tactics library
echo "Searching tactics/library/ for: $QUERY" >&2
TACTICS=$($ENSUE search_memories "{\"query\":\"$QUERY\",\"prefix\":\"tactics/library/\",\"limit\":5}" 2>/dev/null)

# Parse results using jq (cleaner than regex)
# The structuredContent.results[].value contains JSON with name, type, tactic
LEMMAS=$(echo "$TACTICS" | jq -r '
    .result.structuredContent.results[]? |
    select(.key_name | startswith("tactics/library")) |
    .value | fromjson |
    "\(.name)\t\(.type)\t\(.tactic)"
' 2>/dev/null)

if [ -n "$LEMMAS" ]; then
    echo "Found relevant lemmas from collective intelligence:" >&2
    echo "" >&2

    echo "$LEMMAS" | head -5 | while IFS=$'\t' read -r name typ tactic; do
        if [ -n "$name" ]; then
            echo "  LEMMA: $name" >&2
            echo "  TYPE:  $typ" >&2
            echo "  USE:   $tactic" >&2
            echo "" >&2
            echo "$tactic"  # Output to stdout for programmatic use
        fi
    done
else
    echo "No direct matches in tactics library." >&2
fi

# Search for similar solved goals
echo "" >&2
echo "Searching for similar solved goals..." >&2
SIMILAR=$($ENSUE search_memories "{\"query\":\"$QUERY\",\"prefix\":\"proofs/\",\"limit\":3}" 2>/dev/null)

# Parse similar goals with jq
SIMILAR_GOALS=$(echo "$SIMILAR" | jq -r '
    .result.structuredContent.results[]? |
    select(.key_name | contains("/solutions/")) |
    "\(.key_name)\t\(.value)"
' 2>/dev/null)

if [ -n "$SIMILAR_GOALS" ]; then
    echo "Found similar solved goals:" >&2
    echo "$SIMILAR_GOALS" | head -3 | while IFS=$'\t' read -r key val; do
        echo "  $key → $val" >&2
    done
fi

echo "" >&2
echo "=== PRE-VERIFY COMPLETE ===" >&2
echo "Proceed with verification. Try suggested tactics first." >&2

exit 0
