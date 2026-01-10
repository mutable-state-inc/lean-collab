#!/bin/bash
# Heartbeat updater for lean-collab
# Updates agent heartbeat timestamp
# Can be run once or in a loop

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ENSUE_API="$SCRIPT_DIR/ensue-api.sh"

# Get session info
SESSION_FILE="/tmp/lean-collab-session-$$"

# Allow override via arguments
THEOREM_ID="${1:-}"
AGENT_ID="${2:-}"

# Try to load from session file if not provided
if [[ -z "$THEOREM_ID" ]] && [[ -f "$SESSION_FILE" ]]; then
  source "$SESSION_FILE"
fi

if [[ -z "$THEOREM_ID" ]] || [[ -z "$AGENT_ID" ]]; then
  echo '{"error":"No active session. Provide theorem_id and agent_id as arguments."}' >&2
  exit 1
fi

# Update heartbeat
TIMESTAMP=$(date +%s)
RESULT=$(bash "$ENSUE_API" update_memory "{\"key_name\":\"proofs/$THEOREM_ID/agents/$AGENT_ID/heartbeat\",\"value\":\"$TIMESTAMP\"}")

echo "{\"agent_id\":\"$AGENT_ID\",\"timestamp\":$TIMESTAMP,\"status\":\"ok\"}"
