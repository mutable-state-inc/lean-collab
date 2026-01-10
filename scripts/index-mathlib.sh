#!/bin/bash
#
# index-mathlib.sh - Index useful Mathlib lemmas into Ensue collective intelligence
#
# Usage: ./index-mathlib.sh <project_dir> [--background]
#
# This extracts commonly useful lemmas and stores them in Ensue for semantic search.
# Agents can then query: search_memories '{"query":"sin bound concave","prefix":"tactics/library/"}'
#

set -e

PROJECT_DIR="${1:-.}"
BACKGROUND="${2:-}"

# Find Ensue API
ENSUE="$(find ~/.claude/plugins/cache -name 'ensue-api.sh' -path '*/ensue-memory/*' 2>/dev/null | head -1)"

if [ -z "$ENSUE" ]; then
    echo "ERROR: ensue-api.sh not found" >&2
    exit 1
fi

index_lemma() {
    local category="$1"
    local name="$2"
    local type="$3"
    local tactic="$4"

    # Create key with hash to avoid duplicates
    local hash=$(echo -n "$name" | shasum | cut -c1-8)
    local key="tactics/library/$category/$hash"

    # Escape special characters in type for JSON
    type=$(echo "$type" | sed 's/\\/\\\\/g; s/"/\\"/g' | tr '\n' ' ')
    name=$(echo "$name" | sed 's/\\/\\\\/g; s/"/\\"/g')
    tactic=$(echo "$tactic" | sed 's/\\/\\\\/g; s/"/\\"/g')

    # Use create_memory (will fail silently if exists, which is fine)
    $ENSUE create_memory "{\"items\":[{
        \"key_name\":\"$key\",
        \"value\":\"{\\\"name\\\":\\\"$name\\\",\\\"type\\\":\\\"$type\\\",\\\"tactic\\\":\\\"$tactic\\\"}\",
        \"description\":\"$name: $type\",
        \"embed\":true
    }]}" >/dev/null 2>&1
}

# Parse Mathlib source files to extract lemmas
parse_mathlib_files() {
    local category="$1"
    local dir="$2"
    local max_lemmas="${3:-200}"

    echo "Parsing $category from $dir..." >&2

    if [ ! -d "$dir" ]; then
        echo "  Directory not found: $dir" >&2
        return
    fi

    # Extract all theorem/lemma names in one grep pass
    local temp_file=$(mktemp)
    grep -rh "^theorem\|^lemma" "$dir" 2>/dev/null | head -n "$max_lemmas" > "$temp_file"

    local count=0
    while IFS= read -r line; do
        # Extract name (first word after theorem/lemma)
        local name=$(echo "$line" | sed -E 's/^(theorem|lemma)[[:space:]]+([A-Za-z_][A-Za-z0-9_]*).*/\2/')

        if [ -n "$name" ] && [ ${#name} -gt 3 ]; then
            # Get a snippet of the type (text after : up to := or where)
            local type_hint=$(echo "$line" | sed -E 's/.*:[[:space:]]*([^:=]+).*/\1/' | cut -c1-100)

            index_lemma "$category" "$name" "$type_hint" "exact $name"
            count=$((count + 1))
        fi
    done < "$temp_file"

    rm -f "$temp_file"
    echo "  Indexed $count lemmas from $category" >&2
}

# Use Lean's environment to dump lemmas by running #check commands
extract_lemmas_via_lean() {
    local module="$1"
    local category="$2"
    local prefix_filter="$3"

    echo "Extracting $category lemmas from $module..." >&2

    local TEMP_DIR=$(mktemp -d)

    # Create a Lean file that imports the module and checks many lemmas
    cat > "$TEMP_DIR/extract.lean" << EOF
import $module

-- Use environment inspection to find lemmas
-- For now, use explicit #check calls which we can parse

-- Trigonometry
#check @Real.sin_zero
#check @Real.sin_pi
#check @Real.sin_half_pi
#check @Real.sin_neg
#check @Real.sin_add
#check @Real.sin_sub
#check @Real.sin_sq
#check @Real.sin_le_one
#check @Real.neg_one_le_sin
#check @Real.sin_nonneg_of_mem_Icc
#check @Real.sin_pos_of_pos_of_lt_pi
#check @Real.sin_nonneg_of_nonneg_of_le_pi
#check @Real.sin_lt
#check @Real.sin_le_self
#check @Real.two_div_pi_mul_le_sin
#check @Real.sin_sq_add_cos_sq

#check @Real.cos_zero
#check @Real.cos_pi
#check @Real.cos_half_pi
#check @Real.cos_neg
#check @Real.cos_add
#check @Real.cos_sub
#check @Real.cos_sq
#check @Real.cos_le_one
#check @Real.neg_one_le_cos
#check @Real.cos_pos_of_mem_Ioo
#check @Real.cos_nonneg_of_mem_Icc

#check @Real.tan_zero
#check @Real.tan_pi

-- Pi
#check @Real.pi_pos
#check @Real.pi_ne_zero
#check @Real.pi_nonneg
#check @Real.two_pi_pos
#check @Real.pi_gt_three
#check @Real.pi_lt_four

-- Exponential and log
#check @Real.exp_pos
#check @Real.exp_zero
#check @Real.exp_one
#check @Real.exp_add
#check @Real.exp_neg
#check @Real.exp_log
#check @Real.log_exp
#check @Real.log_one
#check @Real.log_mul
#check @Real.log_pow
#check @Real.log_le_sub_one_of_le

-- Square roots and powers
#check @Real.sqrt_nonneg
#check @Real.sqrt_pos
#check @Real.sqrt_sq
#check @Real.sq_sqrt
#check @Real.sqrt_one
#check @Real.sqrt_zero
#check @Real.sqrt_mul

#check @sq_nonneg
#check @sq_pos_of_pos
#check @sq_pos_of_ne_zero
#check @pow_pos
#check @pow_nonneg
#check @pow_two

-- Absolute value
#check @abs_nonneg
#check @abs_pos
#check @abs_of_nonneg
#check @abs_of_nonpos
#check @abs_neg
#check @abs_mul
#check @abs_le

-- Concavity
#check @strictConcaveOn_sin_Icc
#check @StrictConcaveOn.secant_le_self
#check @ConcaveOn.le_right_of_eq_left'
#check @ConvexOn.le_left_of_eq_right'
#check @StrictConvexOn.self_lt_secant
EOF

    cd "$PROJECT_DIR" && lake env lean "$TEMP_DIR/extract.lean" 2>&1 | while read -r line; do
        # Parse #check output: "Name : Type"
        # Handle @ prefix for explicit arguments
        if [[ "$line" =~ ^@?([A-Za-z_][A-Za-z0-9_.]+)[[:space:]]*:[[:space:]]*(.+)$ ]]; then
            local name="${BASH_REMATCH[1]}"
            local type="${BASH_REMATCH[2]}"
            # Clean up type (truncate if too long)
            type=$(echo "$type" | head -c 200)
            index_lemma "$category" "$name" "$type" "exact $name"
        fi
    done

    rm -rf "$TEMP_DIR"
}

# Extract lemmas by grepping Mathlib source for specific patterns
extract_by_grep() {
    local category="$1"
    local pattern="$2"
    local mathlib_dir="$PROJECT_DIR/.lake/packages/mathlib"

    if [ ! -d "$mathlib_dir" ]; then
        echo "Mathlib not found at $mathlib_dir" >&2
        return
    fi

    echo "Grepping Mathlib for $pattern..." >&2

    # Search for theorems/lemmas matching pattern
    local temp_file=$(mktemp)
    grep -rh "^theorem\|^lemma" "$mathlib_dir/Mathlib" 2>/dev/null | \
        grep -i "$pattern" | head -100 > "$temp_file"

    local count=0
    while IFS= read -r line; do
        # Extract name
        local name=$(echo "$line" | sed -E 's/^(theorem|lemma)[[:space:]]+([A-Za-z_][A-Za-z0-9_]*).*/\2/')
        if [ -n "$name" ] && [ ${#name} -gt 3 ]; then
            # Get type hint from the line
            local type_hint=$(echo "$line" | sed -E 's/.*:[[:space:]]*([^:=]+).*/\1/' | cut -c1-100)
            index_lemma "$category" "$name" "$type_hint" "exact $name"
            count=$((count + 1))
        fi
    done < "$temp_file"

    rm -f "$temp_file"
    echo "  Found $count lemmas for $pattern" >&2
}

# Pre-defined useful lemmas (doesn't require Lean)
index_common_lemmas() {
    echo "Indexing common lemmas..." >&2

    # Arithmetic
    index_lemma "arithmetic" "norm_num" "Proves numeric goals" "norm_num"
    index_lemma "arithmetic" "omega" "Linear arithmetic over integers" "omega"
    index_lemma "arithmetic" "ring" "Ring equalities" "ring"
    index_lemma "arithmetic" "linarith" "Linear arithmetic" "linarith"

    # Decidable
    index_lemma "decidable" "native_decide" "Decidable propositions (fast)" "native_decide"
    index_lemma "decidable" "decide" "Decidable propositions" "decide"
    index_lemma "decidable" "rfl" "Reflexivity / definitional equality" "rfl"

    # Analysis - sin bounds
    index_lemma "analysis" "Real.sin_nonneg_of_mem_Icc" "sin x ≥ 0 for x ∈ [0, π]" "exact Real.sin_nonneg_of_mem_Icc hx"
    index_lemma "analysis" "Real.sin_le_one" "sin x ≤ 1" "exact Real.sin_le_one x"
    index_lemma "analysis" "Real.sin_pos_of_pos_of_lt_pi" "sin x > 0 for x ∈ (0, π)" "exact Real.sin_pos_of_pos_of_lt_pi hpos hlt"
    index_lemma "analysis" "Real.two_div_pi_mul_le_sin" "2/π * x ≤ sin x for x ∈ [0, π/2]" "exact Real.two_div_pi_mul_le_sin hx"
    index_lemma "analysis" "Real.pi_pos" "π > 0" "exact Real.pi_pos"
    index_lemma "analysis" "Real.pi_ne_zero" "π ≠ 0" "exact Real.pi_ne_zero"

    # Concavity
    index_lemma "analysis" "strictConcaveOn_sin_Icc" "sin is strictly concave on [0, π]" "exact strictConcaveOn_sin_Icc"

    # Set membership
    index_lemma "sets" "Set.mem_Icc" "x ∈ [a, b] ↔ a ≤ x ∧ x ≤ b" "rw [Set.mem_Icc]"
    index_lemma "sets" "Set.mem_Ioo" "x ∈ (a, b) ↔ a < x ∧ x < b" "rw [Set.mem_Ioo]"

    # Structures
    index_lemma "structures" "constructor" "Split ∧, ∃, structures into subgoals" "constructor"
    index_lemma "structures" "intro" "Introduce ∀ or → hypothesis" "intro x"
    index_lemma "structures" "obtain" "Destruct ∧ or ∃" "obtain ⟨h1, h2⟩ := h"
}

main() {
    echo "=== Mathlib Lemma Indexer ===" >&2
    echo "Storing to Ensue namespace: tactics/library/" >&2

    local MATHLIB_DIR="$PROJECT_DIR/.lake/packages/mathlib"
    local is_lean_project=false

    if [ -f "$PROJECT_DIR/lakefile.lean" ] || [ -f "$PROJECT_DIR/lakefile.toml" ]; then
        is_lean_project=true
    fi

    # Phase 1: Index common tactics and lemmas (fast, no Lean required)
    index_common_lemmas

    # Phase 2: Parse Mathlib source files directly (medium speed)
    if [ -d "$MATHLIB_DIR" ]; then
        echo "=== Parsing Mathlib source files ===" >&2

        # Analysis - trigonometry, calculus, special functions
        parse_mathlib_files "analysis" "$MATHLIB_DIR/Mathlib/Analysis/SpecialFunctions" 100
        parse_mathlib_files "analysis" "$MATHLIB_DIR/Mathlib/Analysis/Calculus" 100
        parse_mathlib_files "analysis" "$MATHLIB_DIR/Mathlib/Analysis/Convex" 50

        # Order theory - supremum, infimum, bounds
        parse_mathlib_files "order" "$MATHLIB_DIR/Mathlib/Order" 100

        # Set theory
        parse_mathlib_files "sets" "$MATHLIB_DIR/Mathlib/Data/Set" 50

        # Real numbers
        parse_mathlib_files "real" "$MATHLIB_DIR/Mathlib/Data/Real" 50

        # Algebra
        parse_mathlib_files "algebra" "$MATHLIB_DIR/Mathlib/Algebra/Order" 50

        # Topology
        parse_mathlib_files "topology" "$MATHLIB_DIR/Mathlib/Topology/Order" 30
    fi

    # Phase 3: Use Lean to extract lemmas with full types (slower but accurate)
    if [ "$is_lean_project" = true ]; then
        echo "=== Extracting via Lean (accurate types) ===" >&2
        extract_lemmas_via_lean "Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic" "analysis/trig"
        extract_lemmas_via_lean "Mathlib.Analysis.Convex.SpecificFunctions.Basic" "analysis/convex"
    fi

    # Phase 4: Grep for specific patterns (supplementary)
    if [ -d "$MATHLIB_DIR" ]; then
        echo "=== Searching for specific patterns ===" >&2
        extract_by_grep "analysis/bounds" "sin.*le\|le.*sin\|cos.*le\|le.*cos"
        extract_by_grep "analysis/inequality" "mul_le\|le_mul\|div_le\|le_div"
        extract_by_grep "order/bounds" "IsLeast\|IsGreatest\|sSup\|sInf"
        extract_by_grep "sets/interval" "Icc\|Ioo\|Ico\|Ioc"
        extract_by_grep "calculus/deriv" "HasDerivAt\|Differentiable\|deriv_"
        extract_by_grep "calculus/cont" "Continuous\|continuous_"
    fi

    echo "=== Indexing complete ===" >&2

    # Show summary
    local count=$($ENSUE list_keys '{"prefix":"tactics/library/","limit":1}' 2>/dev/null | grep -o '"count":[0-9]*' | grep -o '[0-9]*')
    echo "Total lemmas indexed: $count" >&2

    # Show categories
    echo "Categories:" >&2
    $ENSUE list_keys '{"prefix":"tactics/library/","limit":500}' 2>/dev/null | \
        grep -o '"key_name":"[^"]*"' | \
        sed 's/"key_name":"tactics\/library\/\([^/]*\).*/\1/' | \
        sort | uniq -c | sort -rn | head -10 >&2
}

if [ "$BACKGROUND" = "--background" ]; then
    main &
    echo "Indexer running in background (PID: $!)"
else
    main
fi
