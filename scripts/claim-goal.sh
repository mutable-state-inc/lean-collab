#!/bin/bash
#
# claim-goal.sh - Claim a goal with verification
#
# Usage: ./claim-goal.sh <theorem_id> <goal_id> <agent_type> <session_id>
#
# Exit codes:
#   0 - Claimed successfully (verified)
#   1 - Failed to claim (already claimed by another)
#   2 - Error
#

TID="${1:-}"
GID="${2:-}"
AGENT="${3:-agent}"
SID="${4:-$$}"

if [ -z "$TID" ] || [ -z "$GID" ]; then
    echo '{"success":false,"error":"Usage: claim-goal.sh <theorem_id> <goal_id> [agent_type] [session_id]"}' >&2
    exit 2
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
E="$SCRIPT_DIR/ensue-api.sh"

# FIRST: Check if already claimed
CURRENT=$("$E" get_memory "{\"key_names\":[\"proofs/$TID/goals/$GID/status\"]}" 2>/dev/null | jq -r '.result.structuredContent.results[0].value // empty')

if [[ "$CURRENT" == working:* ]]; then
    # Already claimed by someone - fail immediately
    echo "{\"success\":false,\"status\":\"$CURRENT\",\"sid\":\"$SID\",\"error\":\"Already claimed\"}"
    exit 1
fi

# Not claimed yet - attempt to claim
CLAIM_VALUE="working:$AGENT-$SID:$(date +%s)"
"$E" update_memory "{\"key_name\":\"proofs/$TID/goals/$GID/status\",\"value\":\"$CLAIM_VALUE\"}" >/dev/null 2>&1

# Small delay to let writes propagate
sleep 0.1

# Verify claim succeeded (check if our SID is in the status)
VERIFY=$("$E" get_memory "{\"key_names\":[\"proofs/$TID/goals/$GID/status\"]}" 2>/dev/null | jq -r '.result.structuredContent.results[0].value // empty')

if [[ "$VERIFY" == *"$SID"* ]]; then
    echo "{\"success\":true,\"status\":\"$VERIFY\",\"sid\":\"$SID\"}"
    exit 0
else
    echo "{\"success\":false,\"status\":\"$VERIFY\",\"sid\":\"$SID\",\"error\":\"Lost race - claimed by another\"}"
    exit 1
fi
