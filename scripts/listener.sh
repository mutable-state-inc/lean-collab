#!/bin/bash
# SSE Notification Listener for lean-collab
# Connects to Ensue notification service and outputs JSON-RPC notifications
# Usage: ./listener.sh [proof_prefix]
# Example: ./listener.sh proofs/nat-add-comm

PROOF_PREFIX="${1:-proofs/}"

# Get API key
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PLUGIN_ROOT="$(dirname "$SCRIPT_DIR")"
ENSUE_KEY_FILE="$PLUGIN_ROOT/.ensue-key"

if [ -z "$ENSUE_API_KEY" ] && [ -f "$ENSUE_KEY_FILE" ]; then
  ENSUE_API_KEY=$(cat "$ENSUE_KEY_FILE")
fi

if [ -z "$ENSUE_API_KEY" ]; then
  echo '{"error":"ENSUE_API_KEY not set"}' >&2
  exit 1
fi

# Connect to notification service SSE endpoint
# -N: disable buffering for real-time streaming
# Filter output to only include data lines matching our proof prefix
curl -N -s \
  -H "Authorization: Bearer $ENSUE_API_KEY" \
  https://events.ensue-network.ai/mcp 2>/dev/null | \
while IFS= read -r line; do
  # Only process data lines
  if [[ "$line" == data:* ]]; then
    # Extract JSON payload
    json="${line#data: }"

    # Client-side filtering: only output notifications for our proof prefix
    # Extract the URI from the notification
    uri=$(echo "$json" | grep -o '"uri":"[^"]*"' | cut -d'"' -f4)

    # Check if the URI matches our proof prefix (memory:///proofs/...)
    if [[ "$uri" == *"$PROOF_PREFIX"* ]]; then
      echo "$json"
    fi
  fi
done
