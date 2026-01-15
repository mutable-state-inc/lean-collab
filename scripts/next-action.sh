#!/bin/bash
#
# next-action.sh - Determine the next action for the skill
#
# Usage: ./next-action.sh <theorem_id> [--wait]
#
# Without --wait: Returns immediately with current state
# With --wait: Blocks until an actionable event occurs
#
# Output (JSON):
#   {"action":"claim","goals":["goal1","goal2"]}     - Open goals to claim
#   {"action":"compose","goals":[]}                   - All goals done, compose proof
#   {"action":"wait","reason":"..."}                  - Nothing to do right now
#   {"action":"error","message":"..."}                - Error occurred
#

TID="${1:-}"
WAIT_FLAG="${2:-}"

if [ -z "$TID" ]; then
    echo '{"action":"error","message":"Usage: next-action.sh <theorem_id> [--wait]"}'
    exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
E="$SCRIPT_DIR/ensue-api.sh"

# Read max parallel agents from config (default: 9)
MAX_PARALLEL=9
STATE_DIR=""
if [ -f ".lean-collab.json" ]; then
    CONFIGURED=$(cat .lean-collab.json 2>/dev/null | jq -r '.max_parallel_agents // empty')
    [ -n "$CONFIGURED" ] && MAX_PARALLEL="$CONFIGURED"
    STATE_DIR=$(cat .lean-collab.json 2>/dev/null | jq -r '.active_state_dir // empty')
fi

# Get pending spawns (agents spawned but not yet claimed)
PENDING_SPAWNS=0
if [ -n "$STATE_DIR" ] && [ -f "$STATE_DIR/pending_spawns" ]; then
    PENDING_SPAWNS=$(cat "$STATE_DIR/pending_spawns" 2>/dev/null | tr -d '[:space:]')
    [ -z "$PENDING_SPAWNS" ] && PENDING_SPAWNS=0
fi

check_state() {
    # Get all goal status keys
    RESULT=$("$E" list_keys "{\"prefix\":\"proofs/$TID/goals/\",\"limit\":1000}" 2>/dev/null)
    STATUS_KEYS=$(echo "$RESULT" | jq -r '.result.structuredContent.keys[].key_name' 2>/dev/null | grep '/status$')

    if [ -z "$STATUS_KEYS" ]; then
        echo '{"action":"error","message":"No goals found"}'
        return
    fi

    # Parse statuses - batch in chunks of 80 (API limit is 100)
    OPEN_GOALS=""
    ALL_DONE=true
    WORKING_COUNT=0
    STALE_GOALS=""
    NOW=$(date +%s)
    STALE_THRESHOLD=120  # 2 minutes (reduced from 5 for faster recovery)

    # Process keys in batches
    echo "$STATUS_KEYS" > /tmp/status_keys_$$
    TOTAL_KEYS=$(wc -l < /tmp/status_keys_$$ | tr -d ' ')
    BATCH_SIZE=80
    OFFSET=0

    while [ "$OFFSET" -lt "$TOTAL_KEYS" ]; do
        # Get batch of keys
        BATCH_KEYS=$(tail -n +$((OFFSET + 1)) /tmp/status_keys_$$ | head -n $BATCH_SIZE)
        KEY_ARRAY=$(echo "$BATCH_KEYS" | while read key; do echo "\"$key\""; done | tr '\n' ',' | sed 's/,$//')

        # Fetch this batch
        STATUSES=$("$E" get_memory "{\"key_names\":[$KEY_ARRAY]}" 2>/dev/null)

        # Process results
        while IFS= read -r line; do
            [ -z "$line" ] && continue
            KEY=$(echo "$line" | cut -d'|' -f1)
            VAL=$(echo "$line" | cut -d'|' -f2)
            GID=$(echo "$KEY" | sed 's|proofs/[^/]*/goals/||; s|/status||')

            case "$VAL" in
                open|needs_verification|needs_decomposition)
                    OPEN_GOALS="$OPEN_GOALS\"$GID\","
                    ALL_DONE=false
                    ;;
                working:*)
                    CLAIM_TS=$(echo "$VAL" | cut -d':' -f3)
                    if [ -n "$CLAIM_TS" ] && [ "$((NOW - CLAIM_TS))" -gt "$STALE_THRESHOLD" ]; then
                        OPEN_GOALS="$OPEN_GOALS\"$GID\","
                        STALE_GOALS="$STALE_GOALS $GID"
                        ALL_DONE=false
                    else
                        ALL_DONE=false
                        WORKING_COUNT=$((WORKING_COUNT + 1))
                    fi
                    ;;
                solved|decomposed|axiom|solved_by_axiom*|leaf|verified_leaf)
                    ;;
                error:*|blocked:*)
                    ;;
                *)
                    OPEN_GOALS="$OPEN_GOALS\"$GID\","
                    ALL_DONE=false
                    ;;
            esac
        done < <(echo "$STATUSES" | jq -r '.result.structuredContent.results[] | "\(.key_name)|\(.value)"' 2>/dev/null)

        OFFSET=$((OFFSET + BATCH_SIZE))
    done
    rm -f /tmp/status_keys_$$

    # Auto-free stale claims
    for STALE_GID in $STALE_GOALS; do
        "$E" update_memory "{\"key_name\":\"proofs/$TID/goals/$STALE_GID/status\",\"value\":\"open\"}" >/dev/null 2>&1
    done

    # Remove trailing comma
    OPEN_GOALS=$(echo "$OPEN_GOALS" | sed 's/,$//')

    # Calculate available slots (account for pending spawns to prevent thundering herd)
    EFFECTIVE_WORKING=$((WORKING_COUNT + PENDING_SPAWNS))
    AVAILABLE_SLOTS=$((MAX_PARALLEL - EFFECTIVE_WORKING))
    [ "$AVAILABLE_SLOTS" -lt 0 ] && AVAILABLE_SLOTS=0

    if [ -n "$OPEN_GOALS" ] && [ "$AVAILABLE_SLOTS" -gt 0 ]; then
        # Limit goals to available slots
        LIMITED_GOALS=$(echo "$OPEN_GOALS" | tr ',' '\n' | head -n "$AVAILABLE_SLOTS" | tr '\n' ',' | sed 's/,$//')
        TOTAL_OPEN=$(echo "$OPEN_GOALS" | tr ',' '\n' | wc -l | tr -d ' ')
        echo "{\"action\":\"claim\",\"goals\":[$LIMITED_GOALS],\"total_open\":$TOTAL_OPEN,\"slots\":$AVAILABLE_SLOTS,\"working\":$WORKING_COUNT,\"pending\":$PENDING_SPAWNS,\"max\":$MAX_PARALLEL}"
    elif [ -n "$OPEN_GOALS" ] && [ "$AVAILABLE_SLOTS" -le 0 ]; then
        # Have open goals but at capacity (including pending spawns)
        echo "{\"action\":\"wait\",\"reason\":\"at capacity ($WORKING_COUNT working + $PENDING_SPAWNS pending = $EFFECTIVE_WORKING/$MAX_PARALLEL)\",\"queued\":[$OPEN_GOALS]}"
    elif [ "$ALL_DONE" = true ]; then
        echo '{"action":"compose","goals":[]}'
    else
        echo "{\"action\":\"wait\",\"reason\":\"$WORKING_COUNT working + $PENDING_SPAWNS pending\"}"
    fi
}

# Initial check
STATE=$(check_state)
ACTION=$(echo "$STATE" | jq -r '.action' 2>/dev/null)

# If not waiting or we have work to do, return immediately
if [ "$WAIT_FLAG" != "--wait" ] || [ "$ACTION" = "claim" ] || [ "$ACTION" = "compose" ] || [ "$ACTION" = "error" ]; then
    echo "$STATE"
    exit 0
fi

# Wait mode - block until something changes
echo '{"waiting":true,"for":"status change or solution"}' >&2

while true; do
    # Wait for a notification (30s timeout, then recheck)
    EVENT=$("$SCRIPT_DIR/wait-for-event.sh" "$TID" 30 2>/dev/null)
    EXIT_CODE=$?

    # Recheck state after event or timeout
    STATE=$(check_state)
    ACTION=$(echo "$STATE" | jq -r '.action' 2>/dev/null)

    if [ "$ACTION" = "claim" ] || [ "$ACTION" = "compose" ]; then
        echo "$STATE"
        exit 0
    fi

    # Continue waiting if still nothing to do
done
