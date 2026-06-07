/-
Key algebraic lemma for the isqrt correctness proof.

We say that a positive integer `a` is a **near square root** of a positive
integer `n` if `(a - 1)² < n < (a + 1)²`. Equivalently, `a` is either
`⌊√n⌋` or `⌈√n⌉`. The file also defines the companion predicate
`isIntegerSqrt a n` (`a² ≤ n < (a + 1)²`), the exact `a = ⌊√n⌋` postcondition
asserted by the top-level correctness theorems; the algorithm's final
`a-1`/`a` choice is what turns a near square root into the integer square root.

This file proves: given positive integers `n`, `M`, `a` with `4M⁴ ≤ n`,
if `a` is a near square root of `⌊n / 4M²⌋`, then `Ma + ⌊n / 4Ma⌋` is a
near square root of `n`.
-/

import Isqrt.FDivLemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! ## Square-root predicates

Both predicates are stated multiplicatively — `x * x`, never `x ^ 2`:
`isIntegerSqrt` mirrors the Python postcondition `a * a <= n < (a + 1) * (a + 1)`
that the top-level theorems assert, and `isNearSqrt` follows suit for symmetry.
The doc-comment prose, by contrast, writes squares as `x²`: the `*` rule governs
compiled statements that mirror Python source, while informal math in comments
follows ordinary mathematical notation. -/

/-- `a` is a *near square root* of `n` if `(a - 1)² < n < (a + 1)²`.
For positive `n`, this means `a` is either `⌊√n⌋` or `⌈√n⌉`. -/
def isNearSqrt (a n : ℤ) : Prop :=
  (a - 1) * (a - 1) < n ∧ n < (a + 1) * (a + 1)

/-- `a` is *the* integer square root of `n` if `a² ≤ n < (a + 1)²`, i.e.
`a = ⌊√n⌋` exactly — unlike `isNearSqrt`, which only pins `a` down to `⌊√n⌋`
or `⌈√n⌉`. This is the postcondition the top-level correctness theorems
assert. -/
def isIntegerSqrt (a n : ℤ) : Prop := a * a ≤ n ∧ n < (a + 1) * (a + 1)

/-- The algorithm's final return adjustment: a near square root `a` is either
`⌊√n⌋` or `⌈√n⌉`, and subtracting one exactly when `a` overshoots (`n < a * a`)
yields the integer square root. Both correctness proofs close with this step. -/
theorem isNearSqrt.toIntegerSqrt {a n : ℤ} (h : isNearSqrt a n) :
    isIntegerSqrt (if n < a * a then a - 1 else a) n := by
  obtain ⟨h_lo, h_hi⟩ := h
  by_cases h_lt : n < a * a
  · simp only [h_lt, ↓reduceIte]
    exact ⟨by nlinarith [h_lo], by nlinarith [h_lt]⟩
  · simp only [h_lt, ↓reduceIte]
    exact ⟨not_lt.mp h_lt, by nlinarith [h_hi]⟩

/-! ## Algebraic helpers

The Lean 3 versions of these required `sub_elimination` and friends to
handle ℕ subtraction. On ℤ they reduce to `nlinarith` one-liners. -/

/-- If `x` and `y` are within `c` of each other (forcing `c ≥ 1` in ℤ),
then `x² + y² < c² + 2xy`. Equivalent to `(x-y)² < c²`. -/
private theorem close_to {x y c : ℤ} (h1 : x < y + c) (h2 : y < x + c) :
    x^2 + y^2 < c^2 + 2*x*y := by
  have hd1 : 0 ≤ c - 1 - (x - y) := by linarith
  have hd2 : 0 ≤ c - 1 + (x - y) := by linarith
  have hc : 1 ≤ c := by omega
  nlinarith [mul_nonneg hd1 hd2, hc]

/-- If `a ≤ b ≤ c ≤ d`, then `b² + c² + 2ad ≤ a² + d² + 2bc`.
Equivalent to `(d-a)² ≥ (c-b)²`. -/
private theorem square_squeeze {a b c d : ℤ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    b^2 + c^2 + 2*a*d ≤ a^2 + d^2 + 2*b*c := by
  have hd1 : 0 ≤ (d - a) - (c - b) := by linarith
  have hd2 : 0 ≤ (d - a) + (c - b) := by linarith
  nlinarith [mul_nonneg hd1 hd2]

/-! ## Sub-lemmas about the setup -/

/-- `M ≤ a`, given `4M⁴ ≤ n` and `n/(4M²) < (a+1)²`. -/
private theorem M_le_a {n M a : ℤ}
    (hM : 0 < M) (ha : 0 < a) (hM4 : 4 * M^4 ≤ n)
    (ha_hi : n.fdiv (4 * M^2) < (a + 1)^2) :
    M ≤ a := by
  have hdenom : 0 < 4 * M^2 := by positivity
  have h1 : M^2 ≤ n.fdiv (4 * M^2) := by
    rw [Int.le_fdiv_iff_mul_le hdenom]
    nlinarith [hM4]
  have h2 : M^2 < (a + 1)^2 := lt_of_le_of_lt h1 ha_hi
  -- M² < (a+1)² with both positive ⟹ M < a+1 ⟹ M ≤ a
  nlinarith [h2, hM, ha, sq_nonneg (a + 1 - M), sq_nonneg (a + 1 + M)]

/-- `n < 4M²(a+1)²`, restating `ha_hi`. -/
private theorem n_upper {n M a : ℤ} (hM : 0 < M)
    (ha_hi : n.fdiv (4 * M^2) < (a + 1)^2) :
    n < 4 * M^2 * (a + 1)^2 := by
  have hdenom : 0 < 4 * M^2 := by positivity
  have := (Int.fdiv_lt_iff_lt_mul hdenom).mp ha_hi
  linarith

/-- `((a-1)² + 1) · 4M² ≤ n`, restating `ha_lo`. -/
private theorem n_lower {n M a : ℤ} (hM : 0 < M)
    (ha_lo : (a - 1)^2 < n.fdiv (4 * M^2)) :
    ((a - 1)^2 + 1) * (4 * M^2) ≤ n := by
  have hdenom : 0 < 4 * M^2 := by positivity
  rw [← Int.le_fdiv_iff_mul_le hdenom]
  linarith

/-! ## The key lemma -/

/-- If `a` is a near square root of `⌊n / 4M²⌋` and `4M⁴ ≤ n`, then
`Ma + ⌊n / 4Ma⌋` is a near square root of `n`. -/
theorem key_isqrt_lemma {n M a : ℤ}
    (hM : 0 < M) (ha : 0 < a) (hM4 : 4 * M^4 ≤ n)
    (h_near : isNearSqrt a (n.fdiv (4 * M^2))) :
    isNearSqrt (M * a + n.fdiv (4 * M * a)) n := by
  obtain ⟨ha_lo, ha_hi⟩ := h_near
  -- `isNearSqrt` is multiplicative; recover the `^2` shape the algebra uses.
  rw [← pow_two] at ha_lo ha_hi
  set q := n.fdiv (4 * M * a)
  have hMa_pos : 0 < 4 * M * a := by positivity
  have hMa_one : 1 ≤ M * a := by linarith [mul_pos hM ha]
  have hM_le_a : M ≤ a := M_le_a hM ha hM4 ha_hi
  have hn_nonneg : 0 ≤ n := le_trans (by positivity) hM4
  have hq_nonneg : 0 ≤ q := Int.fdiv_nonneg hn_nonneg (le_of_lt hMa_pos)
  -- ===== Upper bound: n < (M*a + q + 1)² =====
  have upper : n < (M * a + q + 1)^2 := by
    -- Floor div upper: n < (q + 1) * (4*M*a)
    have hq_ub : n < (q + 1) * (4 * M * a) := Int.lt_fdiv_add_one_mul hMa_pos
    -- (q + 1) * (4*M*a) ≤ (M*a + q + 1)², since the difference is (M*a - q - 1)² ≥ 0
    nlinarith [hq_ub, sq_nonneg (M * a - q - 1)]
  -- ===== Lower bound: (M*a + q - 1)² < n =====
  have lower : (M * a + q - 1)^2 < n := by
    -- Chain: 4M² ≤ 4Ma ≤ 4M²a² + 4Maq ≤ 4M²a² + n
    have key1 : 4 * M^2 ≤ 4 * M * a := by nlinarith [hM_le_a, hM]
    have key2 : 4 * M * a ≤ 4 * M^2 * a^2 + 4 * M * a * q := by
      nlinarith [hMa_one, hq_nonneg, hM, ha]
    have key3 : 4 * M^2 * a^2 + 4 * M * a * q ≤ 4 * M^2 * a^2 + n := by
      have hqm := Int.fdiv_mul_le_self (x := n) hMa_pos
      nlinarith [hqm]
    have hsq := square_squeeze key1 key2 key3
    -- d_large: n < 4M²a² + 4M² + 8M²a  (rearranged from n_upper)
    have d_large : n < 4 * M^2 * a^2 + 4 * M^2 + 8 * M^2 * a := by
      have := n_upper hM ha_hi
      nlinarith [this]
    -- d_small: 4M²a² + 4M² < n + 8M²a  (rearranged from n_lower)
    have d_small : 4 * M^2 * a^2 + 4 * M^2 < n + 8 * M^2 * a := by
      have := n_lower hM ha_lo
      nlinarith [this]
    have hclose := close_to d_large d_small
    -- The two inequalities provide nonneg "gaps". Their sum equals
    -- `n*(4Ma)² - (M*a + q - 1)²*(4Ma)²` as a polynomial identity (by `ring`),
    -- which gives `(M*a + q - 1)²·(4Ma)² < n·(4Ma)²`.
    have h_sq_gap : 0 ≤
        ((4 * M^2)^2 + (4 * M^2 * a^2 + n)^2
            + 2 * (4 * M * a) * (4 * M^2 * a^2 + 4 * M * a * q))
          - ((4 * M * a)^2 + (4 * M^2 * a^2 + 4 * M * a * q)^2
            + 2 * (4 * M^2) * (4 * M^2 * a^2 + n)) := by linarith [hsq]
    have h_close_gap : 0 <
        ((8 * M^2 * a)^2 + 2 * n * (4 * M^2 * a^2 + 4 * M^2))
          - (n^2 + (4 * M^2 * a^2 + 4 * M^2)^2) := by linarith [hclose]
    have h_identity :
        n * (4 * M * a)^2 - (M * a + q - 1)^2 * (4 * M * a)^2 =
          (((4 * M^2)^2 + (4 * M^2 * a^2 + n)^2
              + 2 * (4 * M * a) * (4 * M^2 * a^2 + 4 * M * a * q))
            - ((4 * M * a)^2 + (4 * M^2 * a^2 + 4 * M * a * q)^2
              + 2 * (4 * M^2) * (4 * M^2 * a^2 + n)))
          + (((8 * M^2 * a)^2 + 2 * n * (4 * M^2 * a^2 + 4 * M^2))
            - (n^2 + (4 * M^2 * a^2 + 4 * M^2)^2)) := by ring
    have h_squared : (M * a + q - 1)^2 * (4 * M * a)^2 < n * (4 * M * a)^2 := by
      linarith [h_sq_gap, h_close_gap, h_identity]
    -- Cancel (4*M*a)²
    have h4Ma_sq_nonneg : (0 : ℤ) ≤ (4 * M * a)^2 := sq_nonneg _
    exact lt_of_mul_lt_mul_right h_squared h4Ma_sq_nonneg
  -- Convert the `^2`-form bounds back to the multiplicative `isNearSqrt`.
  exact ⟨by rw [← pow_two]; exact lower, by rw [← pow_two]; exact upper⟩
