#!/usr/bin/env bash
# lint-lean.sh - Fast syntax linter for Lean (no compilation)
# Usage: ./lint-lean.sh <file.lean>
# Returns: 0 if OK, 1 if issues found

FILE="$1"
if [ ! -f "$FILE" ]; then
  echo "File not found: $FILE" >&2
  exit 2
fi

ERRORS=0

# Check 1: Unmatched brackets
OPEN_PARENS=$(grep -o '(' "$FILE" | wc -l)
CLOSE_PARENS=$(grep -o ')' "$FILE" | wc -l)
if [ "$OPEN_PARENS" -ne "$CLOSE_PARENS" ]; then
  echo "ERROR: Unmatched parentheses ($OPEN_PARENS open, $CLOSE_PARENS close)" >&2
  ERRORS=$((ERRORS + 1))
fi

OPEN_BRACKETS=$(grep -o '\[' "$FILE" | wc -l)
CLOSE_BRACKETS=$(grep -o '\]' "$FILE" | wc -l)
if [ "$OPEN_BRACKETS" -ne "$CLOSE_BRACKETS" ]; then
  echo "ERROR: Unmatched brackets ($OPEN_BRACKETS open, $CLOSE_BRACKETS close)" >&2
  ERRORS=$((ERRORS + 1))
fi

OPEN_BRACES=$(grep -o '{' "$FILE" | wc -l)
CLOSE_BRACES=$(grep -o '}' "$FILE" | wc -l)
if [ "$OPEN_BRACES" -ne "$CLOSE_BRACES" ]; then
  echo "ERROR: Unmatched braces ($OPEN_BRACES open, $CLOSE_BRACES close)" >&2
  ERRORS=$((ERRORS + 1))
fi

# Check 2: Orphan bullets (· without proper context)
# Bullets must be after 'by' or another bullet at same/higher indent
if grep -nE '^[^-]*·' "$FILE" | grep -vE '^\s+·|by$|by\s*$|·\s*--' | head -5 | grep -q .; then
  echo "WARNING: Possible orphan bullets found:" >&2
  grep -nE '^[^-]*·' "$FILE" | grep -vE '^\s+·|by$|by\s*$|·\s*--' | head -3 >&2
fi

# Check 3: Calc chain issues (_ must be on new line)
if grep -nE '[^_]_\s*[<>=≤≥]' "$FILE" | grep -v '^\s*_' | head -3 | grep -q .; then
  echo "WARNING: Calc continuation '_' might need newline:" >&2
  grep -nE '[^_]_\s*[<>=≤≥]' "$FILE" | grep -v '^\s*_' | head -3 >&2
fi

# Check 4: Common typos
if grep -nE '\bby by\b|\bdo do\b|\bthen then\b' "$FILE" | head -3 | grep -q .; then
  echo "WARNING: Duplicate keywords found:" >&2
  grep -nE '\bby by\b|\bdo do\b|\bthen then\b' "$FILE" | head -3 >&2
fi

# Check 5: Tabs (Lean prefers spaces)
if grep -n "$(printf '\t')" "$FILE" | head -3 | grep -q .; then
  echo "WARNING: Tab characters found (use spaces):" >&2
  grep -n "$(printf '\t')" "$FILE" | head -3 >&2
fi

# Check 6: Trailing whitespace before important tokens
if grep -nE '\s+$' "$FILE" | head -3 | grep -q .; then
  # Just a warning, usually OK
  :
fi

if [ $ERRORS -gt 0 ]; then
  echo "Found $ERRORS syntax errors" >&2
  exit 1
fi

echo "Syntax OK"
exit 0
