#!/bin/bash
#
# wait-for-event.sh - Block until a relevant notification arrives
#
# Usage: ./wait-for-event.sh <pattern> [timeout_seconds]
#
# Examples:
#   ./wait-for-event.sh "solutions/"           # Wait for any solution
#   ./wait-for-event.sh "goals/.*/status" 30   # Wait for status change, 30s timeout
#   ./wait-for-event.sh "quadratic-max" 60     # Wait for any event on this theorem
#
# Exit codes:
#   0 - Event matched, outputs the notification JSON
#   1 - Timeout reached
#   2 - Usage error
#
# This script watches /tmp/notifications.log for new entries matching the pattern.
# It remembers the last position and only checks new lines.

PATTERN="${1:-}"
TIMEOUT="${2:-120}"  # Default 2 minutes

if [ -z "$PATTERN" ]; then
    echo "Usage: $0 <pattern> [timeout_seconds]" >&2
    exit 2
fi

# Find notification log - check STATE_DIR first, then /tmp
if [ -n "$STATE_DIR" ] && [ -f "$STATE_DIR/notifications.log" ]; then
    LOGFILE="$STATE_DIR/notifications.log"
elif [ -f "/tmp/notifications.log" ]; then
    LOGFILE="/tmp/notifications.log"
else
    # Find most recent lean-collab session
    LOGFILE=$(ls -t /tmp/lean-collab-*/notifications.log 2>/dev/null | head -1)
    if [ -z "$LOGFILE" ]; then
        LOGFILE="/tmp/notifications.log"  # fallback
    fi
fi
POSFILE="/tmp/notifications.pos.$$"

# Get current end of file (or 0 if doesn't exist)
if [ -f "$LOGFILE" ]; then
    START_POS=$(wc -c < "$LOGFILE" | tr -d ' ')
else
    START_POS=0
fi

# Clean up position file on exit
trap "rm -f $POSFILE" EXIT

START_TIME=$(date +%s)

while true; do
    NOW=$(date +%s)
    ELAPSED=$((NOW - START_TIME))

    if [ "$ELAPSED" -ge "$TIMEOUT" ]; then
        echo '{"timeout":true,"elapsed":'$ELAPSED'}' >&2
        exit 1
    fi

    if [ -f "$LOGFILE" ]; then
        CURRENT_SIZE=$(wc -c < "$LOGFILE" | tr -d ' ')

        if [ "$CURRENT_SIZE" -gt "$START_POS" ]; then
            # New content - check for pattern match
            NEW_CONTENT=$(tail -c +$((START_POS + 1)) "$LOGFILE")

            # Check each line for pattern match
            MATCH=$(echo "$NEW_CONTENT" | grep -E "$PATTERN" | head -1)

            if [ -n "$MATCH" ]; then
                echo "$MATCH"
                exit 0
            fi

            # Update position to current size
            START_POS=$CURRENT_SIZE
        fi
    fi

    # Short sleep to avoid busy-waiting (100ms)
    sleep 0.1
done
