#!/bin/bash
# Refresh subscriptions to all goal status keys
# Called on session start and when goal_index changes
# Usage: ./refresh-subscriptions.sh <theorem_id>

THEOREM_ID="$1"

if [[ -z "$THEOREM_ID" ]]; then
  echo '{"error":"No theorem_id specified"}' >&2
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ENSUE_API="$SCRIPT_DIR/ensue-api.sh"

# List all goals
GOALS_RESPONSE=$(bash "$ENSUE_API" list_keys "{\"prefix\":\"proofs/$THEOREM_ID/goals/\",\"limit\":200}")

# Extract goal IDs and subscribe to each status key
echo "$GOALS_RESPONSE" | grep -o '"key_name":"proofs/[^"]*"' | cut -d'"' -f4 | while read key; do
  # Subscribe to status keys
  if [[ "$key" == */status ]]; then
    bash "$ENSUE_API" subscribe_to_memory "{\"key_name\":\"$key\"}" > /dev/null 2>&1
    echo "Subscribed to $key"
  fi
  # Also subscribe to solution keys so we know when goals are solved
  goal_id=$(echo "$key" | sed 's|proofs/.*/goals/\([^/]*\)/.*|\1|')
  solution_key="proofs/$THEOREM_ID/solutions/$goal_id"
  bash "$ENSUE_API" subscribe_to_memory "{\"key_name\":\"$solution_key\"}" > /dev/null 2>&1
done

echo "Subscription refresh complete for $THEOREM_ID"
