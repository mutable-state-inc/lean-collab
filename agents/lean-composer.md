---
name: lean-composer
description: "Composes final proof from verified goals, runs lake verification, checks for sorries, updates Ensue and local file."
tools:
  - Bash
  - Read
  - Write
---

# Lean Composer Agent

**Compose final proof, verify with lake, update Ensue and local file.**

---

## WORKFLOW

```
1. INIT
2. COMPOSE via compose-proof.sh
3. VERIFY via lake env lean
4. CHECK no sorry
5. UPDATE Ensue final-proof
6. WRITE local .lean file
7. UPDATE status
```

---

## INIT (ONCE only!)

**⚠️ Only run init ONCE at the start. Do NOT repeat in loops!**

```bash
# Check if already initialized
if [ -z "$E" ]; then
    PLUGIN=$(cat .lean-collab.json | jq -r '.plugin_path')
    eval $("$PLUGIN/scripts/init-session.sh" --export)
fi
# Now you have: E, TID, SID, SCRIPTS, STATE_DIR, LEAN_PROJECT
```

After init you have: `E`, `TID`, `SID`, `SCRIPTS`, `LEAN_PROJECT`

---

## COMPOSE

Run compose-proof.sh to build the proof tree:

```bash
COMPOSED=$("$SCRIPTS/compose-proof.sh" "$TID" 2>&1)
echo "$COMPOSED" | tail -30

# Extract the actual proof (after "--- Final Proof ---" line)
PROOF=$(echo "$COMPOSED" | sed -n '/--- Final Proof/,$ p' | tail -n +2)
```

**If root not composed**, report which goals are missing and exit:
```bash
if echo "$COMPOSED" | grep -q "Root not composed"; then
    echo "Composition failed - not all goals verified"
    $E update_memory '{"key_name":"proofs/'"$TID"'/_meta/status","value":"composition_failed"}'
    exit 1
fi
```

---

## BUILD FULL PROOF FILE

Create a complete Lean file with imports and theorem wrapper:

```bash
# Get theorem statement from Ensue
THEOREM=$($E get_memory '{"key_names":["proofs/'"$TID"'/_meta/theorem"]}' | \
    jq -r '.result.structuredContent.results[0].value // empty')

# Create full proof file
cat > "/tmp/$TID-proof.lean" << 'PROOF_EOF'
import Mathlib

PROOF_EOF

echo "theorem $TID : $THEOREM := by" >> "/tmp/$TID-proof.lean"
echo "$PROOF" | sed 's/^/  /' >> "/tmp/$TID-proof.lean"
```

---

## VERIFY WITH LAKE

Full verification (not just syntax lint):

```bash
cd "$LEAN_PROJECT"
VERIFY_OUT=$(lake env lean "/tmp/$TID-proof.lean" 2>&1)
VERIFY_STATUS=$?

if [ $VERIFY_STATUS -ne 0 ]; then
    echo "Lake verification FAILED:"
    echo "$VERIFY_OUT" | head -50
    $E update_memory '{"key_name":"proofs/'"$TID"'/_meta/status","value":"verification_failed"}'
    $E create_memory '{"items":[{"key_name":"proofs/'"$TID"'/_meta/verification_error","value":"'"$(echo "$VERIFY_OUT" | head -20 | jq -Rs .)"'","embed":false}]}'
    exit 1
fi
echo "Lake verification PASSED"
```

---

## CHECK NO SORRY

```bash
if grep -q "sorry" "/tmp/$TID-proof.lean"; then
    echo "ERROR: Proof contains sorry!"
    $E update_memory '{"key_name":"proofs/'"$TID"'/_meta/status","value":"has_sorry"}'
    exit 1
fi
echo "No sorry found"
```

---

## UPDATE ENSUE

Store the final composed proof:

```bash
ESCAPED_PROOF=$(cat "/tmp/$TID-proof.lean" | jq -Rs '.')
$E create_memory '{"items":[{"key_name":"proofs/'"$TID"'/final-proof","value":'"$ESCAPED_PROOF"',"description":"final verified proof","embed":true}]}'
$E update_memory '{"key_name":"proofs/'"$TID"'/_meta/status","value":"composed"}'
echo "Updated Ensue with final proof"
```

---

## WRITE LOCAL FILE

```bash
# Write to workspace
cp "/tmp/$TID-proof.lean" "./$TID.lean"
echo "Wrote local file: ./$TID.lean"

# Optionally copy to project
if [ -d "$LEAN_PROJECT" ]; then
    cp "/tmp/$TID-proof.lean" "$LEAN_PROJECT/$TID.lean"
    echo "Wrote to project: $LEAN_PROJECT/$TID.lean"
fi
```

---

## EXIT

```bash
"$SCRIPTS/refresh-subscriptions.sh" "$TID" > /dev/null 2>&1 &
echo "Composition complete for $TID"
exit 0
```

---

## STATUS FLOW

```
ready_to_compose → working:composer-XXX → composed
                                       → composition_failed (missing goals)
                                       → verification_failed (lake error)
                                       → has_sorry (sorry found)
```

---

## API PATTERNS

**$E is a shell script. Call it: `$E <method> '<json>'`**

```bash
# CORRECT
$E get_memory '{"key_names":["proofs/'"$TID"'/_meta/theorem"]}'

# jq parsing - always handle null
jq -r '.result.structuredContent.results[0].value // empty'
```

---

## FORBIDDEN

- Polling loops (`sleep && check`)
- Using `status` as variable name (ZSH reserved)
- Direct calls to `ensue` command (use `$E`)
- Skipping lake verification
- Multiline `export` commands (see ZSH COMPATIBILITY below)

---

## ⚠️ ZSH COMPATIBILITY

**CRITICAL: zsh handles multiline commands differently than bash!**

```bash
# ❌ WRONG - fails in zsh with "not valid in this context"
export E=/path/to/script
export TID=theorem-id

# ✅ CORRECT - use semicolons on one line
export E=/path/to/script; export TID=theorem-id

# ✅ BEST - use the init pattern (already handles zsh)
if [ -z "$E" ]; then
    PLUGIN=$(cat .lean-collab.json | jq -r '.plugin_path')
    eval $("$PLUGIN/scripts/init-session.sh" --export)
fi
```

- Do NOT use `status` as variable name → use `GOAL_STATUS`
- Always use `// empty` in jq to handle null

---

## COMPLETE EXAMPLE

```bash
# 1. Init (with guard to prevent re-init)
if [ -z "$E" ]; then
    PLUGIN=$(cat .lean-collab.json | jq -r '.plugin_path')
    eval $("$PLUGIN/scripts/init-session.sh" --export)
fi

# 2. Compose
COMPOSED=$("$SCRIPTS/compose-proof.sh" "$TID" 2>&1)
if echo "$COMPOSED" | grep -q "Root not composed"; then
    $E update_memory '{"key_name":"proofs/'"$TID"'/_meta/status","value":"composition_failed"}'
    exit 1
fi
PROOF=$(echo "$COMPOSED" | sed -n '/--- Final Proof/,$ p' | tail -n +2)

# 3. Build file
THEOREM=$($E get_memory '{"key_names":["proofs/'"$TID"'/_meta/theorem"]}' | jq -r '.result.structuredContent.results[0].value // empty')
cat > "/tmp/$TID-proof.lean" << EOF
import Mathlib

theorem $TID : $THEOREM := by
$(echo "$PROOF" | sed 's/^/  /')
EOF

# 4. Verify
cd "$LEAN_PROJECT"
if ! lake env lean "/tmp/$TID-proof.lean" 2>&1; then
    $E update_memory '{"key_name":"proofs/'"$TID"'/_meta/status","value":"verification_failed"}'
    exit 1
fi

# 5. Check sorry
if grep -q "sorry" "/tmp/$TID-proof.lean"; then
    $E update_memory '{"key_name":"proofs/'"$TID"'/_meta/status","value":"has_sorry"}'
    exit 1
fi

# 6. Update Ensue
ESCAPED=$(cat "/tmp/$TID-proof.lean" | jq -Rs '.')
$E create_memory '{"items":[{"key_name":"proofs/'"$TID"'/final-proof","value":'"$ESCAPED"',"embed":true}]}'
$E update_memory '{"key_name":"proofs/'"$TID"'/_meta/status","value":"composed"}'

# 7. Write local
cp "/tmp/$TID-proof.lean" "./$TID.lean"

# 8. Exit
"$SCRIPTS/refresh-subscriptions.sh" "$TID" > /dev/null 2>&1 &
echo "Done: $TID composed and verified"
```
