#!/bin/bash
#
# record-attempt.sh - Record a failed tactic attempt to Ensue
#
# Usage: ./record-attempt.sh <theorem_id> <goal_id> <tactic> <error_msg>
#
# This MUST be called after every failed tactic attempt.
# Failure to record attempts wastes tokens for future agents.

set -e

THEOREM_ID="$1"
GOAL_ID="$2"
TACTIC="$3"
ERROR_MSG="${4:-unknown error}"

if [ -z "$THEOREM_ID" ] || [ -z "$GOAL_ID" ] || [ -z "$TACTIC" ]; then
    echo "Usage: $0 <theorem_id> <goal_id> <tactic> <error_msg>" >&2
    exit 1
fi

# Find Ensue API (local)
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ENSUE="$SCRIPT_DIR/ensue-api.sh"
if [ ! -f "$ENSUE" ]; then
    echo "ERROR: ensue-api.sh not found at $ENSUE" >&2
    exit 1
fi

# Generate unique attempt ID
ATTEMPT_ID="attempt-$(date +%s)-$$"

# Escape JSON special characters
TACTIC_ESC=$(echo "$TACTIC" | sed 's/\\/\\\\/g; s/"/\\"/g' | tr '\n' ' ')
ERROR_ESC=$(echo "$ERROR_MSG" | sed 's/\\/\\\\/g; s/"/\\"/g' | tr '\n' ' ' | cut -c1-200)

# Record to Ensue
KEY="proofs/$THEOREM_ID/goals/$GOAL_ID/attempts/$ATTEMPT_ID"
VALUE="{\"tactic\":\"$TACTIC_ESC\",\"error\":\"$ERROR_ESC\",\"timestamp\":$(date +%s)}"

RESULT=$($ENSUE create_memory "{\"items\":[{
    \"key_name\":\"$KEY\",
    \"value\":\"$VALUE\",
    \"description\":\"verification attempt\",
    \"embed\":false
}]}" 2>&1)

if echo "$RESULT" | grep -q '"isError":false'; then
    echo "Recorded failed attempt: $TACTIC" >&2
    echo "$KEY"  # Output the key for reference
else
    echo "WARNING: Failed to record attempt to Ensue" >&2
    echo "$RESULT" >&2
    exit 1
fi
