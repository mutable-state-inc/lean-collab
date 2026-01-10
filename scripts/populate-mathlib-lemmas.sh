#!/usr/bin/env bash
# populate-mathlib-lemmas.sh - Pre-populate collective intelligence with common Mathlib lemmas
# Usage: ./populate-mathlib-lemmas.sh

E="$(find ~/.claude/plugins/cache -name 'ensue-api.sh' -path '*/ensue-memory/*' 2>/dev/null | head -1)"

if [ -z "$E" ]; then
  echo "Error: ensue-api.sh not found"
  exit 1
fi

echo "=== Populating Mathlib Lemma Library ==="

# Function to add a lemma
add_lemma() {
  local category="$1"
  local name="$2"
  local signature="$3"
  local usage="$4"

  local key="tactics/library/mathlib/$category/$name"
  local value=$(jq -n --arg sig "$signature" --arg use "$usage" --arg name "$name" \
    '{name: $name, signature: $sig, usage: $use}')

  "$E" create_memory "{\"items\":[{\"key_name\":\"$key\",\"value\":$(echo "$value" | jq -Rs '.'),\"description\":\"$name\",\"embed\":true}]}" >/dev/null 2>&1
  echo "  + $name"
}

echo ""
echo "--- Pi Bounds ---"
add_lemma "real/pi" "pi_gt_three" "3 < Real.pi" "exact Real.pi_gt_three"
add_lemma "real/pi" "pi_lt_four" "Real.pi < 4" "exact Real.pi_lt_four"
add_lemma "real/pi" "two_le_pi" "2 ≤ Real.pi" "exact Real.two_le_pi"
add_lemma "real/pi" "pi_pos" "0 < Real.pi" "exact Real.pi_pos"
add_lemma "real/pi" "pi_ne_zero" "Real.pi ≠ 0" "exact Real.pi_ne_zero"

echo ""
echo "--- Trigonometry ---"
add_lemma "real/trig" "sin_lt" "0 < x → sin x < x" "exact Real.sin_lt hx"
add_lemma "real/trig" "sin_pos_of_pos_of_lt_pi" "0 < x → x < π → 0 < sin x" "exact Real.sin_pos_of_pos_of_lt_pi hx hlt"
add_lemma "real/trig" "sin_le_one" "sin x ≤ 1" "exact Real.sin_le_one x"
add_lemma "real/trig" "sin_pi_sub" "sin (π - x) = sin x" "simp [Real.sin_pi_sub]"
add_lemma "real/trig" "cos_pi_sub" "cos (π - x) = -cos x" "simp [Real.cos_pi_sub]"
add_lemma "real/trig" "sin_zero" "sin 0 = 0" "exact Real.sin_zero"
add_lemma "real/trig" "cos_zero" "cos 0 = 1" "exact Real.cos_zero"
add_lemma "real/trig" "sin_pi" "sin π = 0" "exact Real.sin_pi"
add_lemma "real/trig" "cos_pi" "cos π = -1" "exact Real.cos_pi"
add_lemma "real/trig" "sin_pi_div_two" "sin (π/2) = 1" "exact Real.sin_pi_div_two"

echo ""
echo "--- Concavity ---"
add_lemma "analysis/concave" "strictConcaveOn_sin_Icc" "StrictConcaveOn ℝ (Set.Icc 0 π) sin" "exact Real.strictConcaveOn_sin_Icc"
add_lemma "analysis/concave" "concaveOn_sin_Icc" "ConcaveOn ℝ (Set.Icc 0 π) sin" "exact Real.strictConcaveOn_sin_Icc.concaveOn"

echo ""
echo "--- Derivatives ---"
add_lemma "calculus/deriv" "hasDerivAt_sin" "HasDerivAt sin (cos x) x" "exact Real.hasDerivAt_sin x"
add_lemma "calculus/deriv" "hasDerivAt_cos" "HasDerivAt cos (-sin x) x" "exact Real.hasDerivAt_cos x"
add_lemma "calculus/deriv" "deriv_sin" "deriv sin x = cos x" "simp [Real.deriv_sin]"
add_lemma "calculus/deriv" "deriv_cos" "deriv cos x = -sin x" "simp [Real.deriv_cos]"

echo ""
echo "--- Combinatorics ---"
add_lemma "nat/comb" "centralBinom" "Nat.centralBinom n = (2*n).choose n" "rfl"
add_lemma "nat/comb" "choose_symm" "k ≤ n → n.choose (n - k) = n.choose k" "exact Nat.choose_symm h"
add_lemma "nat/comb" "choose_self" "n.choose n = 1" "exact Nat.choose_self n"
add_lemma "nat/comb" "choose_zero_right" "n.choose 0 = 1" "exact Nat.choose_zero_right n"

echo ""
echo "--- Series ---"
add_lemma "series" "hasSum_geometric" "|r| < 1 → HasSum (fun n => r^n) (1 - r)⁻¹" "exact hasSum_geometric_of_lt_one hr.le hr"
add_lemma "series" "tsum_geometric" "|r| < 1 → ∑' n, r^n = (1 - r)⁻¹" "exact tsum_geometric_of_lt_one hr.le hr"
add_lemma "series" "summable_geometric" "|r| < 1 → Summable (fun n => r^n)" "exact summable_geometric_of_lt_one hr.le hr"

echo ""
echo "--- Exponential/Log ---"
add_lemma "real/exp" "exp_pos" "0 < exp x" "exact Real.exp_pos x"
add_lemma "real/exp" "exp_zero" "exp 0 = 1" "exact Real.exp_zero"
add_lemma "real/log" "log_one" "log 1 = 0" "exact Real.log_one"
add_lemma "real/log" "exp_log" "0 < x → exp (log x) = x" "exact Real.exp_log hx"

echo ""
echo "--- Inequalities ---"
add_lemma "ineq" "sq_nonneg" "0 ≤ x^2" "exact sq_nonneg x"
add_lemma "ineq" "sq_pos_of_ne_zero" "x ≠ 0 → 0 < x^2" "exact sq_pos_of_ne_zero x hx"
add_lemma "ineq" "div_pos" "0 < a → 0 < b → 0 < a/b" "exact div_pos ha hb"

echo ""
echo "=== Done ==="
"$E" list_keys '{"prefix":"tactics/library/mathlib/","limit":100}' 2>/dev/null | jq -r '.result.structuredContent.count'
echo "lemmas added to collective intelligence"
