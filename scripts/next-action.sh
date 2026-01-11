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

check_state() {
    # Get all goal statuses in one batch
    RESULT=$("$E" list_keys "{\"prefix\":\"proofs/$TID/goals/\",\"limit\":100}" 2>/dev/null)
    STATUS_KEYS=$(echo "$RESULT" | jq -r '.result.structuredContent.keys[].key_name' 2>/dev/null | grep '/status$')

    if [ -z "$STATUS_KEYS" ]; then
        echo '{"action":"error","message":"No goals found"}'
        return
    fi

    KEY_ARRAY=$(echo "$STATUS_KEYS" | while read key; do echo "\"$key\""; done | tr '\n' ',' | sed 's/,$//')
    STATUSES=$("$E" get_memory "{\"key_names\":[$KEY_ARRAY]}" 2>/dev/null)

    # Parse statuses
    OPEN_GOALS=""
    ALL_DONE=true
    WORKING_COUNT=0

    while IFS= read -r line; do
        KEY=$(echo "$line" | cut -d'|' -f1)
        VAL=$(echo "$line" | cut -d'|' -f2)
        GID=$(echo "$KEY" | sed 's|proofs/[^/]*/goals/||; s|/status||')

        case "$VAL" in
            open|needs_verification|needs_decomposition)
                # These are all claimable states
                OPEN_GOALS="$OPEN_GOALS\"$GID\","
                ALL_DONE=false
                ;;
            working:*)
                ALL_DONE=false
                WORKING_COUNT=$((WORKING_COUNT + 1))
                ;;
            solved|decomposed|solved_by_axiom*)
                # These are terminal states
                ;;
            *)
                # Unknown status - treat as needing attention
                OPEN_GOALS="$OPEN_GOALS\"$GID\","
                ALL_DONE=false
                ;;
        esac
    done < <(echo "$STATUSES" | jq -r '.result.structuredContent.results[] | "\(.key_name)|\(.value)"' 2>/dev/null)

    # Remove trailing comma
    OPEN_GOALS=$(echo "$OPEN_GOALS" | sed 's/,$//')

    if [ -n "$OPEN_GOALS" ]; then
        echo "{\"action\":\"claim\",\"goals\":[$OPEN_GOALS]}"
    elif [ "$ALL_DONE" = true ]; then
        echo '{"action":"compose","goals":[]}'
    else
        echo "{\"action\":\"wait\",\"reason\":\"$WORKING_COUNT goals being worked on\"}"
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
