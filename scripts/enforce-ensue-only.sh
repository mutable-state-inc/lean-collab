#!/bin/bash
# PreToolUse hook: Enforce Ensue-only knowledge access
# All knowledge should come from Ensue, not file searches or reads
# Exit 0 = allow, Exit 2 = block with message

INPUT=$(cat)
TOOL_NAME=$(echo "$INPUT" | jq -r '.tool_name // empty' 2>/dev/null)

case "$TOOL_NAME" in
    "Glob"|"Grep")
        # Block all Glob/Grep - use Ensue search_memories instead
        echo "BLOCKED: Use collective intelligence instead of file search:" >&2
        echo "  \$ENSUE search_memories '{\"query\":\"...\",\"prefix\":\"tactics/library/\"}'" >&2
        exit 2
        ;;

    "Read")
        FILE_PATH=$(echo "$INPUT" | jq -r '.tool_input.file_path // empty' 2>/dev/null)

        # Block reading .lake/ (Mathlib source)
        if echo "$FILE_PATH" | grep -q '\.lake/'; then
            echo "BLOCKED: Do not read Mathlib source. Use collective intelligence." >&2
            exit 2
        fi

        # Block reading .lean files except config and temp verification files
        if echo "$FILE_PATH" | grep -qE '\.lean$'; then
            # Allow temp verification files
            if echo "$FILE_PATH" | grep -qE '^/tmp/|^/var/|/verify.*\.lean$'; then
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
            # Find Ensue API (use cached path if available)
            E=$(cat /tmp/ensue_path.txt 2>/dev/null)
            TID=$(cat /tmp/theorem_id.txt 2>/dev/null)

            if [ -n "$E" ] && [ -n "$TID" ]; then
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

        # ATTEMPT LIMIT: Check for verification file writes via cat heredoc
        # Pattern: cat > /tmp/verify_GOALID.lean
        GOAL_ID=$(echo "$COMMAND" | sed -n "s|.*cat[^>]*>[[:space:]]*/tmp/verify_\([^/.]*\)\.lean.*|\1|p" | head -1)
        if [ -n "$GOAL_ID" ]; then
            E=$(cat /tmp/ensue_path.txt 2>/dev/null)
            TID=$(cat /tmp/theorem_id.txt 2>/dev/null)

            if [ -n "$E" ] && [ -n "$TID" ]; then
                ATTEMPT_COUNT=$("$E" list_keys "{\"prefix\":\"proofs/$TID/attempts/$GOAL_ID/\",\"limit\":10}" 2>/dev/null | jq -r '.result.structuredContent.keys | length' 2>/dev/null || echo "0")

                if [ "$ATTEMPT_COUNT" -ge 3 ]; then
                    echo "BLOCKED: Goal '$GOAL_ID' already has $ATTEMPT_COUNT failed attempts." >&2
                    echo "" >&2
                    echo "  Per protocol, mark as needs_decomposition and move on:" >&2
                    echo "  \$E update_memory '{\"key_name\":\"proofs/$TID/goals/$GOAL_ID/status\",\"value\":\"needs_decomposition\"}'" >&2
                    exit 2
                fi
            fi
        fi
        ;;
esac

exit 0
