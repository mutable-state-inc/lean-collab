#!/bin/bash
# Session end hook for lean-collab
# Cleans up agent state, releases claimed goals

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ENSUE_API="$SCRIPT_DIR/ensue-api.sh"

# Session state file
SESSION_FILE="/tmp/lean-collab-session-$$"

if [[ -f "$SESSION_FILE" ]]; then
  source "$SESSION_FILE"

  if [[ -n "$THEOREM_ID" ]] && [[ -n "$AGENT_ID" ]]; then
    echo "lean-collab: Cleaning up agent $AGENT_ID for $THEOREM_ID"

    # Check if we have any claimed goals and release them
    WORKING_ON_KEY="proofs/$THEOREM_ID/agents/$AGENT_ID/working-on"
    WORKING_ON=$(bash "$ENSUE_API" get_memory "{\"keys\":[\"$WORKING_ON_KEY\"]}" 2>/dev/null | grep -o '"value":"[^"]*"' | head -1 | cut -d'"' -f4)

    if [[ -n "$WORKING_ON" ]] && [[ "$WORKING_ON" != "null" ]]; then
      # Release the claimed goal
      GOAL_STATUS_KEY="proofs/$THEOREM_ID/goals/$WORKING_ON/status"
      bash "$ENSUE_API" update_memory "{\"key_name\":\"$GOAL_STATUS_KEY\",\"value\":\"open\"}" > /dev/null 2>&1
      echo "lean-collab: Released goal $WORKING_ON"
    fi

    # Mark agent as offline (set heartbeat to 0)
    bash "$ENSUE_API" update_memory "{\"key_name\":\"proofs/$THEOREM_ID/agents/$AGENT_ID/heartbeat\",\"value\":\"0\"}" > /dev/null 2>&1

    # Clear working-on
    bash "$ENSUE_API" update_memory "{\"key_name\":\"$WORKING_ON_KEY\",\"value\":\"\"}" > /dev/null 2>&1

    echo "lean-collab: Agent $AGENT_ID signed off"
  fi

  # Cleanup session file
  rm -f "$SESSION_FILE"
fi

# Kill any lingering listener processes for this session
pkill -f "lean-collab.*listener.*$$" 2>/dev/null || true

exit 0
