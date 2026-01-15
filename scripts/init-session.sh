#!/bin/bash
#
# init-session.sh - Initialize a session-isolated state directory
#
# Usage: source $(./init-session.sh)
#        Or: eval $(./init-session.sh --export)
#
# Creates /tmp/lean-collab-$SID/ with all state files
# Outputs the STATE_DIR path (or exports variables with --export)
#

set -e

# Read config
CONFIG=".lean-collab.json"
if [ ! -f "$CONFIG" ]; then
    echo "ERROR: $CONFIG not found" >&2
    exit 1
fi

TID=$(cat "$CONFIG" | jq -r '.theorem_id // empty')
PLUGIN=$(cat "$CONFIG" | jq -r '.plugin_path // empty')
LEAN_PROJECT=$(cat "$CONFIG" | jq -r '.lean_project // empty')
MAX_DEPTH=$(cat "$CONFIG" | jq -r '.max_depth // 8')

if [ -z "$TID" ] || [ -z "$PLUGIN" ]; then
    echo "ERROR: theorem_id or plugin_path missing from $CONFIG" >&2
    exit 1
fi

if [ -z "$LEAN_PROJECT" ]; then
    echo "WARNING: lean_project not set in $CONFIG - Lean verification will fail" >&2
fi

E="$PLUGIN/scripts/ensue-api.sh"
SCRIPTS="$PLUGIN/scripts"

# Persist API key for subagents (they don't inherit env vars)
ENSUE_KEY_FILE="$PLUGIN/.ensue-key"
if [ -n "$ENSUE_API_KEY" ] && [ ! -f "$ENSUE_KEY_FILE" ]; then
    echo "$ENSUE_API_KEY" > "$ENSUE_KEY_FILE"
    chmod 600 "$ENSUE_KEY_FILE"
fi

# Generate session ID
SID=$(head -c 6 /dev/urandom | base64 | tr -dc 'a-zA-Z0-9' | head -c 8)

# Create session-specific state directory
STATE_DIR="/tmp/lean-collab-$SID"
mkdir -p "$STATE_DIR"

# Initialize spawn tracking (prevents thundering herd OOM)
echo "0" > "$STATE_DIR/pending_spawns"

# Write state files (both formats for compatibility)
echo "$E" > "$STATE_DIR/ensue_path.txt"
echo "$TID" > "$STATE_DIR/theorem_id.txt"
echo "$SCRIPTS" > "$STATE_DIR/scripts_path.txt"
echo "$SID" > "$STATE_DIR/session_id.txt"
echo "$STATE_DIR" > "$STATE_DIR/state_dir.txt"
echo "$LEAN_PROJECT" > "$STATE_DIR/lean_project.txt"
echo "$MAX_DEPTH" > "$STATE_DIR/max_depth.txt"

# Write session.json for session-end.sh
cat > "$STATE_DIR/session.json" << EOF
{"theorem_id":"$TID","session_id":"$SID","state_dir":"$STATE_DIR","created":$(date +%s),"created_by_pid":"$$"}
EOF

# Store active session in .lean-collab.json so subagents can find it
TMP=$(mktemp)
jq --arg sd "$STATE_DIR" --arg sid "$SID" '. + {active_state_dir: $sd, active_session_id: $sid}' "$CONFIG" > "$TMP" && mv "$TMP" "$CONFIG"

# Start notification listener (shared per theorem, not per session)
# Use a global PID file to prevent listener accumulation
LISTENER_PID_FILE="/tmp/lean-collab-listener-$TID.pid"

# Kill any existing listeners for this theorem first
pkill -f "listener.sh proofs/$TID" 2>/dev/null || true
sleep 0.2

# Start fresh listener
nohup bash "$SCRIPTS/listener.sh" "proofs/$TID" > "$STATE_DIR/notifications.log" 2>&1 &
LISTENER_PID=$!
echo $LISTENER_PID > "$LISTENER_PID_FILE"
echo $LISTENER_PID > "$STATE_DIR/listener.pid"

# Subscribe to existing goals
bash "$SCRIPTS/refresh-subscriptions.sh" "$TID" > "$STATE_DIR/subscriptions.log" 2>&1 &

if [ "$1" = "--export" ]; then
    # Output export commands for eval
    echo "export STATE_DIR='$STATE_DIR'"
    echo "export E='$E'"
    echo "export TID='$TID'"
    echo "export SCRIPTS='$SCRIPTS'"
    echo "export SID='$SID'"
    echo "export LEAN_PROJECT='$LEAN_PROJECT'"
    echo "export MAX_DEPTH='$MAX_DEPTH'"
else
    # Just output the state dir path
    echo "$STATE_DIR"
fi
