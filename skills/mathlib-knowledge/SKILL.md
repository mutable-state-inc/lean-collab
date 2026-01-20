---
name: mathlib-knowledge
description: "Deep Mathlib and mathematical reasoning knowledge for lean-prover agents."
---

# Mathlib Knowledge Base

**This skill provides strategic mathematical knowledge. Use it to find the RIGHT lemma and the CLEVER approach.**

---

## Core Philosophy

1. **Don't reinvent** - Mathlib has 99% of what you need
2. **Name patterns matter** - Lemmas follow predictable naming conventions
3. **Work backwards** - Know your target form, find lemmas that produce it
4. **Hypothesis hunting** - Most lemmas need specific hypotheses; gather them first

---

## Tactic Decision Tree

```
GOAL TYPE                           → FIRST TRY
─────────────────────────────────────────────────
Pure numeric (0 < 5, 3 * 4 = 12)   → norm_num
Decidable prop (finite check)       → decide, native_decide
Equality with ring ops              → ring, ring_nf
Linear arithmetic (ℤ, ℕ, ℚ)        → omega
Polynomial inequality               → polyrith (needs import)
Nonlinear with hints                → nlinarith [hint1, hint2]
Set membership                      → simp, exact ⟨_, _⟩
Trivial from hypothesis             → exact h, assumption
Rewrite needed                      → rw [lemma], simp only [lemma]
Function application                → apply lemma, refine lemma ?_ ?_
Split conjunction                   → constructor, ⟨_, _⟩
Existential                         → use witness, refine ⟨witness, ?_⟩
```

---

## Mathlib Naming Conventions

**Learn these patterns - they unlock the library:**

### Operations
| Pattern | Meaning | Example |
|---------|---------|---------|
| `add_` | About addition | `add_comm`, `add_assoc` |
| `mul_` | About multiplication | `mul_comm`, `mul_one` |
| `sub_` | About subtraction | `sub_self`, `sub_add_cancel` |
| `div_` | About division | `div_self`, `div_mul_cancel` |
| `pow_` | About powers | `pow_zero`, `pow_succ` |
| `neg_` | About negation | `neg_neg`, `neg_add` |
| `inv_` | About inverse | `inv_inv`, `mul_inv_cancel` |

### Relations
| Pattern | Meaning | Example |
|---------|---------|---------|
| `_le_` | Less or equal | `add_le_add`, `mul_le_mul` |
| `_lt_` | Strictly less | `add_lt_add`, `mul_lt_mul` |
| `_eq_` | Equality | `add_eq_zero`, `mul_eq_one` |
| `_ne_` | Not equal | `mul_ne_zero` |
| `_pos` | Positive | `mul_pos`, `add_pos` |
| `_neg` | Negative | `mul_neg`, `neg_neg_of_pos` |
| `_nonneg` | Non-negative | `mul_nonneg`, `sq_nonneg` |
| `_nonpos` | Non-positive | `mul_nonpos_of_nonneg_of_nonpos` |

### Transformations
| Pattern | Meaning | Example |
|---------|---------|---------|
| `_of_` | Derives from | `le_of_lt`, `pos_of_ne_zero` |
| `_iff_` | Biconditional | `lt_iff_le_not_le` |
| `_comm` | Commutativity | `add_comm`, `mul_comm` |
| `_assoc` | Associativity | `add_assoc`, `mul_assoc` |
| `_cancel` | Cancellation | `add_left_cancel`, `mul_right_cancel` |
| `_inj` | Injectivity | `add_left_inj` |

### Structures
| Pattern | Meaning | Example |
|---------|---------|---------|
| `IsLeast` | Minimum element | `IsLeast.mem`, `IsLeast.le` |
| `IsGreatest` | Maximum element | `IsGreatest.mem`, `IsGreatest.le` |
| `Monotone` | Order preserving | `Monotone.comp` |
| `StrictMono` | Strictly increasing | `StrictMono.lt_iff_lt` |
| `Convex` | Convex set/function | `ConvexOn.le_right` |
| `Concave` | Concave function | `ConcaveOn.le_left` |

---

## Critical Lemmas by Domain

### Real Analysis (`Mathlib.Analysis.SpecialFunctions`)

**Sine and Cosine:**
```lean
Real.sin_zero : sin 0 = 0
Real.sin_pi : sin π = 0
Real.cos_zero : cos 0 = 1
Real.cos_pi : cos π = -1
Real.sin_nonneg_of_mem_Icc : x ∈ Icc 0 π → 0 ≤ sin x
Real.sin_pos_of_mem_Ioo : x ∈ Ioo 0 π → 0 < sin x
Real.sin_le_one : sin x ≤ 1
Real.neg_one_le_sin : -1 ≤ sin x
```

**Exponential and Logarithm:**
```lean
Real.exp_zero : exp 0 = 1
Real.exp_pos : 0 < exp x
Real.exp_lt_exp : exp x < exp y ↔ x < y
Real.log_exp : log (exp x) = x
Real.exp_log (h : 0 < x) : exp (log x) = x
Real.log_mul (hx : 0 < x) (hy : 0 < y) : log (x * y) = log x + log y
Real.log_one : log 1 = 0
Real.log_lt_log (hx : 0 < x) : log x < log y ↔ x < y
```

**Pi:**
```lean
Real.pi_pos : 0 < π
Real.pi_gt_three : 3 < π
Real.pi_lt_four : π < 4
Real.two_le_pi : 2 ≤ π
```

### Inequalities (`Mathlib.Algebra.Order`)

**The Big Three - Memorize These:**
```lean
-- AM-GM (Arithmetic-Geometric Mean)
add_div_two_ge_sqrt_mul (ha : 0 ≤ a) (hb : 0 ≤ b) :
  (a + b) / 2 ≥ √(a * b)

-- Cauchy-Schwarz
inner_mul_le_norm_mul_norm : |⟪x, y⟫| ≤ ‖x‖ * ‖y‖

-- Triangle Inequality
norm_add_le : ‖x + y‖ ≤ ‖x‖ + ‖y‖
abs_add : |a + b| ≤ |a| + |b|
```

**Squares and Positivity:**
```lean
sq_nonneg x : 0 ≤ x^2                    -- ALWAYS use this
sq_abs x : |x|^2 = x^2
sq_le_sq' (h1 : -a ≤ b) (h2 : b ≤ a) : b^2 ≤ a^2
mul_self_nonneg : 0 ≤ a * a
add_pow_le_pow_mul_pow_of_sq_le_sq       -- for (a+b)^n bounds
```

**Monotonicity Helpers:**
```lean
mul_le_mul_of_nonneg_left (h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c
mul_le_mul_of_nonneg_right (h : b ≤ c) (a0 : 0 ≤ a) : b * a ≤ c * a
div_le_div_of_nonneg_left (h : b ≤ c) (a0 : 0 ≤ a) (c0 : 0 < c) : a / c ≤ a / b
```

### Convexity (`Mathlib.Analysis.Convex`)

**The Secret Weapon for Transcendental Inequalities:**
```lean
-- If f is concave on [a,b], then f lies ABOVE the secant line
ConcaveOn.le_right_of_lt_left (hf : ConcaveOn ℝ (Icc a b) f)
  (ha : a < x) (hx : x ≤ b) :
  f x ≥ f a + (f b - f a) / (b - a) * (x - a)

-- If f is convex, then f lies BELOW the secant line
ConvexOn.le_left_of_lt_right (hf : ConvexOn ℝ (Icc a b) f)
  (hx : a ≤ x) (xb : x < b) :
  f x ≤ f a + (f b - f a) / (b - a) * (x - a)
```

**Key Concavity Facts:**
```lean
strictConcaveOn_sin_Icc : StrictConcaveOn ℝ (Icc 0 π) sin
strictConcaveOn_cos_Icc : StrictConcaveOn ℝ (Icc (-π/2) (π/2)) cos
strictConvexOn_exp : StrictConvexOn ℝ univ exp
strictConcaveOn_log_Ioi : StrictConcaveOn ℝ (Ioi 0) log
```

**Using Concavity for sin x ≥ linear bounds:**
```lean
-- sin is concave on [0,π], so sin x ≥ secant line from (0,0) to (π,0)
-- The secant is y = 0, not useful
-- Better: secant from (0,0) to (π/2, 1) gives sin x ≥ (2/π)x on [0,π/2]
-- This is the "Jordan's inequality" technique
```

### Sets and Intervals (`Mathlib.Order.Interval`)

```lean
-- Membership
Set.mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b
Set.mem_Ioo : x ∈ Ioo a b ↔ a < x ∧ x < b
Set.mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b

-- Subset relations
Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b
Icc_subset_Icc (h1 : a' ≤ a) (h2 : b ≤ b') : Icc a b ⊆ Icc a' b'

-- Endpoints
left_mem_Icc : a ∈ Icc a b ↔ a ≤ b
right_mem_Icc : b ∈ Icc a b ↔ a ≤ b
```

### Number Theory (`Mathlib.NumberTheory`)

```lean
Nat.prime_def_lt : p.Prime ↔ 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1
Nat.Prime.one_lt : p.Prime → 1 < p
Nat.Prime.ne_one : p.Prime → p ≠ 1
Nat.exists_prime_and_dvd (h : 2 ≤ n) : ∃ p, p.Prime ∧ p ∣ n
Nat.factors_prime : p ∈ n.factors → p.Prime
```

---

## Strategic Patterns

### Pattern 1: Prove Inequality via Monotonicity
```
Goal: f(a) ≤ f(b) where a ≤ b

Strategy:
1. Find/prove: Monotone f (or MonotoneOn f S)
2. Apply: Monotone.le_of_le or MonotoneOn.le_of_le
```

### Pattern 2: Prove Inequality via Convexity
```
Goal: f(x) ≤ g(x) where g is linear

Strategy:
1. Check: Is f convex? Then f ≤ secant line
2. Check: Is f concave? Then f ≥ secant line
3. Use: ConvexOn.le_right or ConcaveOn.le_right
```

### Pattern 3: Prove Bound via Known Bounds
```
Goal: a ≤ f(x) ≤ b

Strategy:
1. Find intermediate: a ≤ g(x) ≤ f(x) or f(x) ≤ h(x) ≤ b
2. Chain with: le_trans, lt_of_le_of_lt, lt_of_lt_of_le
```

### Pattern 4: Prove Equality via Squeeze
```
Goal: f(x) = c

Strategy:
1. Prove: f(x) ≤ c (upper bound)
2. Prove: c ≤ f(x) (lower bound)
3. Apply: le_antisymm
```

### Pattern 5: Prove Positivity
```
Goal: 0 < f(x)

Strategy:
1. If product: mul_pos h1 h2
2. If sum of positives: add_pos h1 h2
3. If square: sq_pos_of_ne_zero h
4. If exponential: exp_pos x
5. If specific: pi_pos, one_pos, etc.
```

### Pattern 6: Transcendental Inequality
```
Goal: sin x ≤ polynomial(x) on interval

Strategy:
1. Use concavity: sin is concave on [0,π]
2. Compare to secant line between key points
3. Apply: strictConcaveOn_sin_Icc.concaveOn.le_right
4. Compute: endpoint values to verify secant bound
```

---

## nlinarith Mastery

`nlinarith` is your workhorse for nonlinear arithmetic. Feed it the right hints:

```lean
-- Basic pattern
nlinarith [sq_nonneg x, sq_nonneg y, h1, h2]

-- Common hints to include:
sq_nonneg x          -- x^2 ≥ 0
sq_nonneg (x - y)    -- (x-y)^2 ≥ 0, expands to x^2 - 2xy + y^2 ≥ 0
mul_self_nonneg x    -- x * x ≥ 0
sq_abs x             -- |x|^2 = x^2
abs_nonneg x         -- 0 ≤ |x|

-- From hypotheses
mul_nonneg h1 h2     -- if h1 : 0 ≤ a, h2 : 0 ≤ b, then 0 ≤ a*b
mul_pos h1 h2        -- if h1 : 0 < a, h2 : 0 < b, then 0 < a*b
```

**Pro tip:** If nlinarith fails, try:
1. Adding more `sq_nonneg` hints
2. Multiplying inequalities: `have := mul_nonneg h1 h2`
3. Rewriting to simpler form first: `ring_nf` then `nlinarith`

---

## Common Proof Skeletons

### Proving IsLeast/IsGreatest
```lean
example : IsLeast S x := by
  constructor
  · -- Membership: x ∈ S
    simp [S]  -- or exact ⟨_, _⟩
  · -- Minimality: ∀ y ∈ S, x ≤ y
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    nlinarith  -- or omega, linarith
```

### Proving ∀ x ∈ Interval
```lean
example : ∀ x ∈ Icc a b, P x := by
  intro x hx
  obtain ⟨ha, hb⟩ := hx  -- ha : a ≤ x, hb : x ≤ b
  -- now prove P x using ha, hb
```

### Proving Existential with Specific Witness
```lean
example : ∃ x ∈ S, P x := by
  use 42        -- the witness
  constructor
  · norm_num    -- 42 ∈ S
  · ring        -- P 42
```

---

## Debugging Failed Tactics

| Tactic | Common Failure | Fix |
|--------|----------------|-----|
| `norm_num` | Non-numeric terms | Extract numeric part, prove separately |
| `ring` | Non-ring structure | Check for division, use `field_simp` first |
| `nlinarith` | Missing nonlinear facts | Add `sq_nonneg`, `mul_pos` hints |
| `omega` | Non-integer types | Only works on ℤ, ℕ, convert first |
| `simp` | Wrong lemmas | Use `simp only [specific_lemmas]` |
| `exact` | Type mismatch | Check implicit arguments with `@exact` |

---

## Import Checklist

If a lemma isn't found, you may need these imports:

```lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic -- sin, cos
import Mathlib.Analysis.SpecialFunctions.Exp -- exp, log
import Mathlib.Analysis.SpecialFunctions.Pow.Real -- rpow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic -- convexity of exp, etc.
import Mathlib.Analysis.MeanInequalities -- AM-GM, etc.
import Mathlib.Order.Bounds.Basic -- IsLeast, IsGreatest
import Mathlib.Topology.Order.Basic -- continuity + order
```

---

## Quick Reference Card

```
GOAL                          TACTIC
────────────────────────────────────────
0 < 5                         norm_num
x + y = y + x                 ring
a ≤ b → b ≤ c → a ≤ c        exact le_trans h1 h2
0 ≤ x^2                       exact sq_nonneg x
x ∈ Icc 0 1                   exact ⟨by norm_num, by norm_num⟩
P ∧ Q                         exact ⟨hP, hQ⟩  or  constructor
∃ x, P x                      exact ⟨witness, proof⟩  or  use witness
sin x ≤ 1                     exact Real.sin_le_one x
0 < π                         exact Real.pi_pos
exp 0 = 1                     exact Real.exp_zero
f concave, bound needed       ConcaveOn.le_right ...
x^2 + y^2 ≥ 0                 nlinarith [sq_nonneg x, sq_nonneg y]
```
