#!/bin/bash
#
# load-session.sh - Load session state from STATE_DIR
#
# Usage: eval $(./load-session.sh /tmp/lean-collab-XYZ)
#        Or: eval $(./load-session.sh)  # uses STATE_DIR env var
#
# Outputs export commands for: E, TID, SCRIPTS, SID, STATE_DIR
#

STATE_DIR="${1:-$STATE_DIR}"

if [ -z "$STATE_DIR" ]; then
    # Try to find from config
    CONFIG=".lean-collab.json"
    if [ -f "$CONFIG" ]; then
        PLUGIN=$(cat "$CONFIG" | jq -r '.plugin_path // empty')
        TID=$(cat "$CONFIG" | jq -r '.theorem_id // empty')
        E="$PLUGIN/scripts/ensue-api.sh"
        SCRIPTS="$PLUGIN/scripts"
        SID=$(head -c 6 /dev/urandom | base64 | tr -dc 'a-zA-Z0-9' | head -c 8)
        STATE_DIR="/tmp/lean-collab-$SID"
        mkdir -p "$STATE_DIR"
        echo "$E" > "$STATE_DIR/ensue_path.txt"
        echo "$TID" > "$STATE_DIR/theorem_id.txt"
        echo "$SCRIPTS" > "$STATE_DIR/scripts_path.txt"
        echo "$SID" > "$STATE_DIR/session_id.txt"
    else
        echo "echo 'ERROR: No STATE_DIR and no .lean-collab.json'" >&2
        exit 1
    fi
else
    if [ ! -d "$STATE_DIR" ]; then
        echo "echo 'ERROR: STATE_DIR not found: $STATE_DIR'" >&2
        exit 1
    fi
    E=$(cat "$STATE_DIR/ensue_path.txt" 2>/dev/null)
    TID=$(cat "$STATE_DIR/theorem_id.txt" 2>/dev/null)
    SCRIPTS=$(cat "$STATE_DIR/scripts_path.txt" 2>/dev/null)
    SID=$(cat "$STATE_DIR/session_id.txt" 2>/dev/null)
fi

echo "export STATE_DIR='$STATE_DIR'"
echo "export E='$E'"
echo "export TID='$TID'"
echo "export SCRIPTS='$SCRIPTS'"
echo "export SID='$SID'"
