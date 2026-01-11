#!/bin/bash
# PreToolUse hook: Enforce Ensue-only knowledge access
# All knowledge should come from Ensue, not file searches or reads
# Exit 0 = allow, Exit 2 = block with message

INPUT=$(cat)
TOOL_NAME=$(echo "$INPUT" | jq -r '.tool_name // empty' 2>/dev/null)

# Helper: Get Ensue API path and theorem ID from .lean-collab.json
get_ensue_config() {
    if [ -f ".lean-collab.json" ]; then
        PLUGIN=$(cat .lean-collab.json | jq -r '.plugin_path // empty' 2>/dev/null)
        TID=$(cat .lean-collab.json | jq -r '.theorem_id // empty' 2>/dev/null)
        if [ -n "$PLUGIN" ]; then
            E="$PLUGIN/scripts/ensue-api.sh"
            export E TID
            return 0
        fi
    fi
    # Fallback to CLAUDE_PLUGIN_ROOT
    if [ -n "$CLAUDE_PLUGIN_ROOT" ]; then
        E="$CLAUDE_PLUGIN_ROOT/scripts/ensue-api.sh"
        export E
        return 0
    fi
    return 1
}

case "$TOOL_NAME" in
    "Glob"|"Grep")
        # Block all Glob/Grep - use Ensue search_memories instead
        echo "BLOCKED: Use collective intelligence instead of file search:" >&2
        echo "  \$ENSUE search_memories '{\"query\":\"...\",\"prefix\":\"tactics/library/\"}'" >&2
        exit 2
        ;;

    "Read")
        FILE_PATH=$(echo "$INPUT" | jq -r '.tool_input.file_path // empty' 2>/dev/null)

        # Block reading other agent output files
        if echo "$FILE_PATH" | grep -qE '/tasks/[a-f0-9]+\.output|/claude.*\.output'; then
            echo "BLOCKED: Do not read other agent output files!" >&2
            echo "" >&2
            echo "  Use Ensue notifications instead:" >&2
            echo "  tail -n 20 /tmp/notifications.log | grep \"\$TID\"" >&2
            echo "  \$E get_memory '{\"key_names\":[\"proofs/\$TID/goals/GOAL/status\"]}'" >&2
            exit 2
        fi

        # Block reading .lake/ (Mathlib source)
        if echo "$FILE_PATH" | grep -q '\.lake/'; then
            echo "BLOCKED: Do not read Mathlib source. Use collective intelligence." >&2
            exit 2
        fi

        # Block reading .lean files except config, temp, and main theorem files
        if echo "$FILE_PATH" | grep -qE '\.lean$'; then
            # Allow temp verification files
            if echo "$FILE_PATH" | grep -qE '^/tmp/|^/var/|/verify.*\.lean$'; then
                exit 0
            fi
            # Allow main theorem file in project root (skill needs to read it for initial setup)
            # Pattern: TheoremName.lean (capital letter start) - handles relative and absolute paths
            BASENAME=$(basename "$FILE_PATH")
            if echo "$BASENAME" | grep -qE '^[A-Z][a-zA-Z0-9_]*\.lean$'; then
                exit 0
            fi
            # Allow .lean-collab.json and CLAUDE.md
            if echo "$FILE_PATH" | grep -qE 'lean-collab\.json|CLAUDE\.md'; then
                exit 0
            fi
            echo "BLOCKED: Do not read project .lean files. Get goal info from Ensue:" >&2
            echo "  \$ENSUE get_memory '{\"key_names\":[\"proofs/{TID}/goals/{GID}/definition\"]}'" >&2
            exit 2
        fi
        ;;

    "Write")
        FILE_PATH=$(echo "$INPUT" | jq -r '.tool_input.file_path // empty' 2>/dev/null)
        CONTENT=$(echo "$INPUT" | jq -r '.tool_input.content // empty' 2>/dev/null)

        # Only allow writing to temp directories for verification
        if ! echo "$FILE_PATH" | grep -qE '^/tmp/|^/var/'; then
            echo "BLOCKED: Only write to /tmp/ for verification. Record results to Ensue." >&2
            exit 2
        fi

        LINE_COUNT=$(echo "$CONTENT" | wc -l)

        # Allow unlimited size for composed/final proofs - these are outputs, not exploration
        if echo "$FILE_PATH" | grep -qiE '(composed|final|complete|full|proof).*\.lean$'; then
            # No limit for final proof files - they can be as long as needed
            exit 0
        fi

        # ATTEMPT LIMIT: Check if goal already has 3+ failed attempts
        # Filename must be /tmp/verify_{GOAL_ID}.lean to enable tracking
        GOAL_ID=$(echo "$FILE_PATH" | sed -n 's|.*/verify_\([^/]*\)\.lean$|\1|p')
        if [ -n "$GOAL_ID" ]; then
            # Get Ensue API path from config
            if get_ensue_config; then
                # Check attempt count
                ATTEMPT_COUNT=$("$E" list_keys "{\"prefix\":\"proofs/$TID/attempts/$GOAL_ID/\",\"limit\":10}" 2>/dev/null | jq -r '.result.structuredContent.keys | length' 2>/dev/null || echo "0")

                if [ "$ATTEMPT_COUNT" -ge 3 ]; then
                    echo "BLOCKED: Goal '$GOAL_ID' already has $ATTEMPT_COUNT failed attempts." >&2
                    echo "" >&2
                    echo "  Per protocol, you must:" >&2
                    echo "  1. Mark goal as needs_decomposition" >&2
                    echo "  2. Move to a different goal" >&2
                    echo "" >&2
                    echo "  Command:" >&2
                    echo "  \$E update_memory '{\"key_name\":\"proofs/$TID/goals/$GOAL_ID/status\",\"value\":\"needs_decomposition\"}'" >&2
                    exit 2
                fi
            fi
        fi

        # Block overly long verification files (>100 lines for single goals)
        # This limit only applies to single-goal verification, not final proofs
        if [ "$LINE_COUNT" -gt 100 ]; then
            echo "BLOCKED: Verification file too long ($LINE_COUNT lines)." >&2
            echo "" >&2
            echo "  If this is a SINGLE GOAL: decompose it further (>100 lines = too complex)" >&2
            echo "" >&2
            echo "  If this is a FINAL PROOF: rename to include 'proof' in the filename:" >&2
            echo "    /tmp/putnam_proof.lean" >&2
            echo "    /tmp/final_proof.lean" >&2
            echo "    /tmp/a2_complete_proof.lean" >&2
            exit 2
        fi
        ;;

    "Bash")
        COMMAND=$(echo "$INPUT" | jq -r '.tool_input.command // empty' 2>/dev/null)

        # BLOCK READING OTHER AGENT OUTPUT FILES
        if echo "$COMMAND" | grep -qE '(tail|cat|head|less|grep).*(/tasks/[a-f0-9]+\.output|/claude.*/tasks/)'; then
            echo "BLOCKED: Do not read other agent output files!" >&2
            echo "" >&2
            echo "  Use Ensue notifications instead:" >&2
            echo "  tail -n 20 /tmp/notifications.log | grep \"\$TID\"" >&2
            echo "  \$E get_memory '{\"key_names\":[\"proofs/\$TID/goals/GOAL/status\"]}'" >&2
            exit 2
        fi

        # BLOCK HARDCODED CACHE PATHS
        # Agents must use plugin_path from .lean-collab.json, not hardcoded cache paths
        if echo "$COMMAND" | grep -qE '\.claude/plugins/cache.*ensue'; then
            echo "BLOCKED: Do not hardcode cache paths!" >&2
            echo "" >&2
            echo "  Use the local plugin path from .lean-collab.json:" >&2
            echo "" >&2
            echo '  PLUGIN=$(cat .lean-collab.json | jq -r ".plugin_path")' >&2
            echo '  E="$PLUGIN/scripts/ensue-api.sh"' >&2
            exit 2
        fi

        # Block grep/rg/find on mathlib
        if echo "$COMMAND" | grep -qE '(grep|rg|find).*\.lake'; then
            echo "BLOCKED: Do not search Mathlib. Use collective intelligence." >&2
            exit 2
        fi

        # Block cat/head/tail on .lake
        if echo "$COMMAND" | grep -qE '(cat|head|tail|less).*\.lake'; then
            echo "BLOCKED: Do not read Mathlib source." >&2
            exit 2
        fi

        # COORDINATION: Block claiming already-claimed goals (unless stale >30 mins)
        STALE_THRESHOLD=1800  # 30 minutes in seconds
        if echo "$COMMAND" | grep -qE 'update_memory.*status.*working:'; then
            # Extract TID and GOAL_ID from command: proofs/THEOREM_ID/goals/GOAL_ID/status
            FULL_PATH=$(echo "$COMMAND" | grep -oE 'proofs/[^/]+/goals/[^/]+/status' | head -1)
            TID=$(echo "$FULL_PATH" | sed 's|proofs/||; s|/goals/.*||')
            GOAL_ID=$(echo "$FULL_PATH" | sed 's|proofs/[^/]*/goals/||; s|/status||')

            if [ -n "$GOAL_ID" ] && [ -n "$TID" ]; then
                # Find ensue-api.sh from plugin path
                E="$CLAUDE_PLUGIN_ROOT/scripts/ensue-api.sh"
                if [ -f "$E" ]; then
                    GOAL_STATUS=$("$E" get_memory "{\"key_names\":[\"proofs/$TID/goals/$GOAL_ID/status\"]}" 2>/dev/null | jq -r '.result.structuredContent.results[0].value // empty')
                    if [[ "$GOAL_STATUS" =~ ^working: ]]; then
                        # Extract timestamp from working:agent:TIMESTAMP
                        CLAIM_TS=$(echo "$GOAL_STATUS" | sed 's/.*://')
                        NOW_TS=$(date +%s)
                        AGE=$((NOW_TS - CLAIM_TS))

                        if [ "$AGE" -lt "$STALE_THRESHOLD" ]; then
                            MINS_LEFT=$(( (STALE_THRESHOLD - AGE) / 60 ))
                            echo "BLOCKED: Goal '$GOAL_ID' already claimed!" >&2
                            echo "" >&2
                            echo "  Current status: $GOAL_STATUS" >&2
                            echo "  Claimed $((AGE / 60)) mins ago (stale after 30 mins, $MINS_LEFT mins left)" >&2
                            echo "" >&2
                            echo "  Another agent is working on this. Pick a different goal." >&2
                            exit 2
                        else
                            echo "OVERRIDE: Claim on '$GOAL_ID' is stale ($((AGE / 60)) mins old). Allowing re-claim." >&2
                        fi
                    fi
                fi
            fi
        fi

        # COORDINATION: Block creating child goals without claiming parent first
        if echo "$COMMAND" | grep -qE 'create_memory.*goals/[^/]+/children'; then
            # Extract TID and GOAL_ID from command
            FULL_PATH=$(echo "$COMMAND" | grep -oE 'proofs/[^/]+/goals/[^/]+/children' | head -1)
            TID=$(echo "$FULL_PATH" | sed 's|proofs/||; s|/goals/.*||')
            GOAL_ID=$(echo "$FULL_PATH" | sed 's|proofs/[^/]*/goals/||; s|/children||')

            if [ -n "$GOAL_ID" ] && [ -n "$TID" ]; then
                E="$CLAUDE_PLUGIN_ROOT/scripts/ensue-api.sh"
                if [ -f "$E" ]; then
                    GOAL_STATUS=$("$E" get_memory "{\"key_names\":[\"proofs/$TID/goals/$GOAL_ID/status\"]}" 2>/dev/null | jq -r '.result.structuredContent.results[0].value // empty')
                    if [[ ! "$GOAL_STATUS" =~ ^working: ]]; then
                        echo "BLOCKED: Cannot decompose - goal '$GOAL_ID' not claimed!" >&2
                        echo "" >&2
                        echo "  Current status: $GOAL_STATUS" >&2
                        echo "" >&2
                        echo "  CLAIM the goal first, then decompose:" >&2
                        echo "  \$E update_memory '{\"key_name\":\"proofs/$TID/goals/$GOAL_ID/status\",\"value\":\"working:\$AGENT:\$(date +%s)\"}'" >&2
                        exit 2
                    fi
                fi
            fi
        fi

        # COORDINATION: Block setting final status without claiming first
        # Final statuses: decomposed, solved, abandoned, needs_decomposition
        if echo "$COMMAND" | grep -qE 'update_memory.*status.*(decomposed|solved|abandoned|needs_decomposition)'; then
            GOAL_ID=$(echo "$COMMAND" | grep -oE 'goals/[^/]+/status' | head -1 | sed 's|goals/||; s|/status||')
            if [ -n "$GOAL_ID" ] && get_ensue_config; then
                GOAL_STATUS=$("$E" get_memory "{\"key_names\":[\"proofs/$TID/goals/$GOAL_ID/status\"]}" 2>/dev/null | jq -r '.result.structuredContent.results[0].value // empty')
                if [[ ! "$GOAL_STATUS" =~ ^working: ]]; then
                    echo "BLOCKED: Cannot set final status - goal '$GOAL_ID' not claimed!" >&2
                    echo "" >&2
                    echo "  Current status: $GOAL_STATUS" >&2
                    echo "" >&2
                    echo "  You must CLAIM the goal first:" >&2
                    echo "  \$E update_memory '{\"key_name\":\"proofs/$TID/goals/$GOAL_ID/status\",\"value\":\"working:\$AGENT:\$(date +%s)\"}'" >&2
                    echo "" >&2
                    echo "  Then you can set final status after completing work." >&2
                    exit 2
                fi
            fi
        fi

        # COORDINATION: Block solution submission on unclaimed goals
        if echo "$COMMAND" | grep -qE 'create_memory.*solutions/|update_memory.*solutions/'; then
            GOAL_ID=$(echo "$COMMAND" | grep -oE 'solutions/[^"]+' | head -1 | sed 's|solutions/||')
            if [ -n "$GOAL_ID" ] && get_ensue_config; then
                GOAL_STATUS=$("$E" get_memory "{\"key_names\":[\"proofs/$TID/goals/$GOAL_ID/status\"]}" 2>/dev/null | jq -r '.result.structuredContent.results[0].value // empty')
                if [[ ! "$GOAL_STATUS" =~ ^working: ]]; then
                    echo "BLOCKED: Cannot submit solution - goal '$GOAL_ID' not claimed!" >&2
                    echo "" >&2
                    echo "  Current status: $GOAL_STATUS" >&2
                    echo "" >&2
                    echo "  Claim the goal first, then submit." >&2
                    exit 2
                fi
            fi
        fi

        # ATTEMPT LIMIT: Check for verification file writes via cat heredoc
        # Pattern: cat > /tmp/verify_GOALID.lean
        GOAL_ID=$(echo "$COMMAND" | sed -n "s|.*cat[^>]*>[[:space:]]*/tmp/verify_\([^/.]*\)\.lean.*|\1|p" | head -1)
        if [ -n "$GOAL_ID" ] && get_ensue_config; then
            ATTEMPT_COUNT=$("$E" list_keys "{\"prefix\":\"proofs/$TID/attempts/$GOAL_ID/\",\"limit\":10}" 2>/dev/null | jq -r '.result.structuredContent.keys | length' 2>/dev/null || echo "0")

            if [ "$ATTEMPT_COUNT" -ge 3 ]; then
                echo "BLOCKED: Goal '$GOAL_ID' already has $ATTEMPT_COUNT failed attempts." >&2
                echo "" >&2
                echo "  Per protocol, mark as needs_decomposition and move on:" >&2
                echo "  \$E update_memory '{\"key_name\":\"proofs/$TID/goals/$GOAL_ID/status\",\"value\":\"needs_decomposition\"}'" >&2
                exit 2
            fi
        fi
        ;;
esac

exit 0
