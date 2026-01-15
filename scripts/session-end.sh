#!/bin/bash
# Session end hook for lean-collab
# Cleans up agent state, releases claimed goals
#
# Note: Only releases claims made by THIS specific agent (by matching SID in status)
# The orchestrator's session-end does full cleanup when it exits

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ENSUE_API="$SCRIPT_DIR/ensue-api.sh"

# Get session info - check multiple sources
STATE_DIR="${LEAN_COLLAB_STATE_DIR:-}"
CONFIG=".lean-collab.json"

# Try to find session info
THEOREM_ID=""
SESSION_ID=""
IS_ORCHESTRATOR=false

if [[ -n "$STATE_DIR" ]] && [[ -f "$STATE_DIR/session.json" ]]; then
  THEOREM_ID=$(jq -r '.theorem_id // empty' "$STATE_DIR/session.json" 2>/dev/null)
  SESSION_ID=$(jq -r '.session_id // empty' "$STATE_DIR/session.json" 2>/dev/null)
  # Check if we're the orchestrator (we created this state dir)
  CREATED_BY_PID=$(jq -r '.created_by_pid // empty' "$STATE_DIR/session.json" 2>/dev/null)
  [[ "$CREATED_BY_PID" == "$$" ]] && IS_ORCHESTRATOR=true
elif [[ -f "$CONFIG" ]]; then
  THEOREM_ID=$(jq -r '.theorem_id // empty' "$CONFIG" 2>/dev/null)
  SESSION_ID=$(jq -r '.active_session_id // empty' "$CONFIG" 2>/dev/null)
  STATE_DIR=$(jq -r '.active_state_dir // empty' "$CONFIG" 2>/dev/null)
fi

# Release any claims held by this session
if [[ -n "$THEOREM_ID" ]] && [[ -n "$SESSION_ID" ]]; then
  # Find all goals claimed by this session (status contains our SID)
  RESULT=$(bash "$ENSUE_API" list_keys "{\"prefix\":\"proofs/$THEOREM_ID/goals/\",\"limit\":500}" 2>/dev/null)
  STATUS_KEYS=$(echo "$RESULT" | jq -r '.result.structuredContent.keys[].key_name' 2>/dev/null | grep '/status$')

  RELEASED=0
  for KEY in $STATUS_KEYS; do
    VAL=$(bash "$ENSUE_API" get_memory "{\"key_names\":[\"$KEY\"]}" 2>/dev/null | jq -r '.result.structuredContent.results[0].value // empty')

    # Check if this claim belongs to our session (contains our SID)
    if [[ "$VAL" == *"$SESSION_ID"* ]]; then
      bash "$ENSUE_API" update_memory "{\"key_name\":\"$KEY\",\"value\":\"open\"}" > /dev/null 2>&1
      GID=$(echo "$KEY" | sed 's|.*/goals/||; s|/status||')
      echo "lean-collab: Released $GID" >&2
      RELEASED=$((RELEASED + 1))
    fi
  done

  [[ $RELEASED -gt 0 ]] && echo "lean-collab: Released $RELEASED claims" >&2
fi

# Only do full cleanup if we're the orchestrator
if [[ "$IS_ORCHESTRATOR" == "true" ]] && [[ -n "$STATE_DIR" ]] && [[ -d "$STATE_DIR" ]]; then
  echo "lean-collab: Orchestrator ending, cleaning up state" >&2

  # Kill listener
  [[ -f "$STATE_DIR/listener.pid" ]] && kill $(cat "$STATE_DIR/listener.pid") 2>/dev/null

  # Clear active session from config
  if [[ -f "$CONFIG" ]]; then
    TMP=$(mktemp)
    jq 'del(.active_state_dir, .active_session_id)' "$CONFIG" > "$TMP" 2>/dev/null && mv "$TMP" "$CONFIG"
  fi

  # Remove state directory
  rm -rf "$STATE_DIR"
fi

# Legacy cleanup
SESSION_FILE="/tmp/lean-collab-session-$$"
[[ -f "$SESSION_FILE" ]] && rm -f "$SESSION_FILE"

exit 0
