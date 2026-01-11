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

if [ -z "$TID" ] || [ -z "$PLUGIN" ]; then
    echo "ERROR: theorem_id or plugin_path missing from $CONFIG" >&2
    exit 1
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

# Write state files
echo "$E" > "$STATE_DIR/ensue_path.txt"
echo "$TID" > "$STATE_DIR/theorem_id.txt"
echo "$SCRIPTS" > "$STATE_DIR/scripts_path.txt"
echo "$SID" > "$STATE_DIR/session_id.txt"
echo "$STATE_DIR" > "$STATE_DIR/state_dir.txt"

# Start notification listener
nohup bash "$SCRIPTS/listener.sh" "proofs/$TID" > "$STATE_DIR/notifications.log" 2>&1 &
echo $! > "$STATE_DIR/listener.pid"

# Subscribe to existing goals
bash "$SCRIPTS/refresh-subscriptions.sh" "$TID" > "$STATE_DIR/subscriptions.log" 2>&1 &

if [ "$1" = "--export" ]; then
    # Output export commands for eval
    echo "export STATE_DIR='$STATE_DIR'"
    echo "export E='$E'"
    echo "export TID='$TID'"
    echo "export SCRIPTS='$SCRIPTS'"
    echo "export SID='$SID'"
else
    # Just output the state dir path
    echo "$STATE_DIR"
fi
