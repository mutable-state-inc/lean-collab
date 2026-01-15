#!/bin/bash
#
# spawn-track.sh - Track pending agent spawns to prevent over-allocation
#
# Usage:
#   spawn-track.sh start [STATE_DIR]    - Increment pending spawn count (call BEFORE spawning agent)
#   spawn-track.sh claimed [STATE_DIR]  - Decrement pending (call when agent claims goal)
#   spawn-track.sh count [STATE_DIR]    - Get current pending count
#   spawn-track.sh reset [STATE_DIR]    - Reset to 0 (use sparingly)
#
# The pending count represents agents that have been spawned but haven't yet
# claimed a goal. This prevents the thundering herd problem where fast-finishing
# agents cause more agents to spawn before the first batch is fully tracked.
#

ACTION="${1:-count}"
STATE_DIR="${2:-}"

# Find state dir from config if not provided
if [ -z "$STATE_DIR" ]; then
    if [ -f ".lean-collab.json" ]; then
        STATE_DIR=$(cat .lean-collab.json 2>/dev/null | jq -r '.active_state_dir // empty')
    fi
fi

if [ -z "$STATE_DIR" ] || [ ! -d "$STATE_DIR" ]; then
    echo "0"
    exit 0
fi

PENDING_FILE="$STATE_DIR/pending_spawns"
LOCK_FILE="$STATE_DIR/pending_spawns.lock"

# Simple file-based locking
lock() {
    local timeout=5
    local start=$(date +%s)
    while ! mkdir "$LOCK_FILE" 2>/dev/null; do
        if [ $(($(date +%s) - start)) -ge $timeout ]; then
            # Stale lock, break it
            rm -rf "$LOCK_FILE" 2>/dev/null
            mkdir "$LOCK_FILE" 2>/dev/null || true
            break
        fi
        sleep 0.05
    done
}

unlock() {
    rm -rf "$LOCK_FILE" 2>/dev/null
}

get_count() {
    if [ -f "$PENDING_FILE" ]; then
        local count=$(cat "$PENDING_FILE" 2>/dev/null | tr -d '[:space:]')
        [ -n "$count" ] && echo "$count" || echo "0"
    else
        echo "0"
    fi
}

case "$ACTION" in
    start)
        lock
        COUNT=$(get_count)
        NEW_COUNT=$((COUNT + 1))
        echo "$NEW_COUNT" > "$PENDING_FILE"
        unlock
        echo "$NEW_COUNT"
        ;;
    claimed)
        lock
        COUNT=$(get_count)
        NEW_COUNT=$((COUNT > 0 ? COUNT - 1 : 0))
        echo "$NEW_COUNT" > "$PENDING_FILE"
        unlock
        echo "$NEW_COUNT"
        ;;
    count)
        echo "$(get_count)"
        ;;
    reset)
        lock
        echo "0" > "$PENDING_FILE"
        unlock
        echo "0"
        ;;
    *)
        echo "Usage: spawn-track.sh {start|claimed|count|reset} [STATE_DIR]" >&2
        exit 1
        ;;
esac
