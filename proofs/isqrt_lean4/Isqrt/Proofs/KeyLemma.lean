/-
The isqrt correctness proof's pure-integer mathematics: near-square-root theory and the
Newton-step key lemma. It is all general `Int` arithmetic — the bit-level encoding the
algorithm divides by (shifts, powers of two) lives in `Isqrt.Proofs.PythonTranslation`.

The **near square root** predicate, `isNearSquareRoot` (`(a - 1)² < n < (a + 1)²`; for
positive `n`, `a` is `⌊√n⌋` or `⌈√n⌉`), is defined in `Isqrt.Definitions.Specification`
beside its postcondition `isIntegerSquareRoot`. This file supplies what the correctness
proofs need about it — that a near square root is positive, and the final `a-1`/`a` choice
that turns one into the integer square root — and proves the key combining step:

given positive integers `n`, `M`, `a` with `4M⁴ ≤ n`, if `a` is a near square root of
`⌊n / 4M²⌋`, then `Ma + ⌊n / 4Ma⌋` is a near square root of `n`.
-/

module

public import Isqrt.Definitions.Specification
import Isqrt.Proofs.SupportLemmas

/-! ## Positivity -/

/-- A near square root is positive: `(a-1)² < n < (a+1)²` forces `(a-1)² < (a+1)²`,
i.e. `4a > 0`. -/
public theorem isNearSquareRoot.pos {n a : Int} (h : isNearSquareRoot n a) : 0 < a := by
  obtain ⟨h_lo, h_hi⟩ := h
  grind only

/-! ## From near square root to integer square root -/

/-- The algorithm's final return adjustment: a near square root `a` is either
`⌊√n⌋` or `⌈√n⌉`, and subtracting one exactly when `a` overshoots (`n < a * a`)
yields the integer square root. Both correctness proofs close with this step. -/
public theorem isNearSquareRoot.toIntegerSquareRoot {a n : Int} (h : isNearSquareRoot n a) :
    isIntegerSquareRoot n (if n < a * a then a - 1 else a) := by
  obtain ⟨h_lo, h_hi⟩ := h
  by_cases h_lt : n < a * a
  · simp only [h_lt, ↓reduceIte]
    exact ⟨Int.le_of_lt h_lo, by grind only⟩
  · simp only [h_lt, ↓reduceIte]
    exact ⟨Int.not_lt.mp h_lt, h_hi⟩

/-! ## Algebraic helpers -/

/-- If `x` and `y` are within `c` of each other, then `x² + y² < c² + 2xy`
(equivalently, `(x-y)² < c²`). -/
theorem close_to {x y c : Int} (h1 : x < y + c) (h2 : y < x + c) :
    x^2 + y^2 < c^2 + 2*x*y := by
  -- `|x - y| < c`: both `c ± (x - y)` are positive.
  have hp1 : 0 < c - (x - y) := by omega
  have hp2 : 0 < c + (x - y) := by omega
  -- Their product is `c² - (x-y)²`, i.e. exactly `(c² + 2xy) - (x² + y²)`.
  have factor : (c - (x - y)) * (c + (x - y)) = c^2 + 2*x*y - (x^2 + y^2) := by grind only
  exact Int.sub_pos.mp (factor ▸ Int.mul_pos hp1 hp2)

/-- If `a ≤ b ≤ c ≤ d`, then `b² + c² + 2ad ≤ a² + d² + 2bc`.
Equivalent to `(d-a)² ≥ (c-b)²`. -/
theorem square_squeeze {a b c d : Int}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    b^2 + c^2 + 2*a*d ≤ a^2 + d^2 + 2*b*c := by
  -- `0 ≤ c - b ≤ d - a`: both `(d-a) ± (c-b)` are nonneg.
  have hd1 : 0 ≤ (d - a) - (c - b) := by omega
  have hd2 : 0 ≤ (d - a) + (c - b) := by omega
  -- Their product is `(d-a)² - (c-b)²`, i.e. `(a² + d² + 2bc) - (b² + c² + 2ad)`.
  have factor : ((d - a) - (c - b)) * ((d - a) + (c - b))
      = a^2 + d^2 + 2*b*c - (b^2 + c^2 + 2*a*d) := by grind only
  exact Int.sub_nonneg.mp (factor ▸ Int.mul_nonneg hd1 hd2)

/-- For integers, `x² < y²` with `0 ≤ y` gives `x < y`. -/
theorem lt_of_sq_lt_sq {x y : Int} (hy : 0 ≤ y) (h : x ^ 2 < y ^ 2) : x < y := by
  obtain hlt | hle := Int.lt_or_le x y
  · exact hlt
  · -- `y ≤ x` with `0 ≤ y` forces `y² ≤ x²`, contradicting `h`.
    have hx : 0 ≤ x := Int.le_trans hy hle
    have factor : (x - y) * (x + y) = x ^ 2 - y ^ 2 := by grind only
    have hsq : y ^ 2 ≤ x ^ 2 :=
      Int.sub_nonneg.mp (factor ▸ Int.mul_nonneg (by omega) (by omega))
    exact absurd h (Int.not_lt.mpr hsq)

/-- The AM–GM inequality for two integers: `4xy ≤ (x+y)²` (equivalently `0 ≤ (x−y)²`). -/
theorem four_mul_le_add_sq (x y : Int) : 4 * x * y ≤ (x + y) ^ 2 := by
  have factor : (x - y) ^ 2 = (x + y) ^ 2 - 4 * x * y := by grind only
  exact Int.sub_nonneg.mp (factor ▸ Int.sq_nonneg (x - y))

/-! ## Sub-lemmas about the setup -/

/-- `M ≤ a`, given `4M⁴ ≤ n` and `n/(4M²) < (a+1)²`. -/
theorem M_le_a {n M a : Int}
    (hM : 0 < M) (ha : 0 < a) (hM4 : 4 * M^4 ≤ n)
    (ha_hi : n.fdiv (4 * M^2) < (a + 1)^2) :
    M ≤ a := by
  have hdenom : 0 < 4 * M^2 := Int.mul_pos (by decide) (Int.pow_pos hM)
  have h1 : M^2 ≤ n.fdiv (4 * M^2) := by
    rw [Int.le_fdiv_iff_mul_le hdenom, show M^2 * (4 * M^2) = 4 * M^4 from by grind only]
    exact hM4
  have h2 : M^2 < (a + 1)^2 := Int.lt_of_le_of_lt h1 ha_hi
  -- `M² < (a+1)²` with `a+1 ≥ 0` gives `M < a+1`, hence `M ≤ a`.
  have : M < a + 1 := lt_of_sq_lt_sq (by omega) h2
  omega

/-- `n < 4M²(a+1)²`, restating `ha_hi`. -/
theorem n_upper {n M a : Int} (hM : 0 < M)
    (ha_hi : n.fdiv (4 * M^2) < (a + 1)^2) :
    n < 4 * M^2 * (a + 1)^2 := by
  have hdenom : 0 < 4 * M^2 := Int.mul_pos (by decide) (Int.pow_pos hM)
  have := (Int.fdiv_lt_iff_lt_mul hdenom).mp ha_hi
  grind only

/-- `((a-1)² + 1) · 4M² ≤ n`, restating `ha_lo`. -/
theorem n_lower {n M a : Int} (hM : 0 < M)
    (ha_lo : (a - 1)^2 < n.fdiv (4 * M^2)) :
    ((a - 1)^2 + 1) * (4 * M^2) ≤ n := by
  have hdenom : 0 < 4 * M^2 := Int.mul_pos (by decide) (Int.pow_pos hM)
  rw [← Int.le_fdiv_iff_mul_le hdenom]
  grind only

/-! ## Suitable scalers -/

/-- `M` is a *suitable scaler* for `n`: it is positive and `4M⁴ ≤ n`. That bound is the
sense in which `M` is "small enough" — equivalently `M² ≤ ⌊n / 4M²⌋`. -/
@[expose] public def isSuitableScaler (n M : Int) : Prop := 0 < M ∧ 4 * M^4 ≤ n

/-! ## The key lemma -/

/-- If `M` is a suitable scaler for `n` and `a` is a near square root of `⌊n / 4M²⌋`, then
`Ma + ⌊n / 4Ma⌋` is a near square root of `n`. -/
public theorem key_isqrt_lemma {n M a : Int}
    (hM_scaler : isSuitableScaler n M)
    (h_near : isNearSquareRoot (n.fdiv (4 * M^2)) a) :
    isNearSquareRoot n (M * a + n.fdiv (4 * M * a)) := by
  obtain ⟨hM, hM4⟩ := hM_scaler
  have ha : 0 < a := h_near.pos
  obtain ⟨ha_lo, ha_hi⟩ := h_near
  -- `isNearSquareRoot` is multiplicative; recover the `^2` shape the algebra uses.
  rw [show (a - 1) * (a - 1) = (a - 1) ^ 2 from by grind only] at ha_lo
  rw [show (a + 1) * (a + 1) = (a + 1) ^ 2 from by grind only] at ha_hi
  let q := n.fdiv (4 * M * a)
  have hMa_pos : 0 < 4 * M * a := Int.mul_pos (Int.mul_pos (by decide) hM) ha
  have hMa_one : 1 ≤ M * a := by have := Int.mul_pos hM ha; grind only
  have hM_le_a : M ≤ a := M_le_a hM ha hM4 ha_hi
  have h4M4_nonneg : 0 ≤ 4 * M^4 :=
    Int.mul_nonneg (by decide) (Int.pow_nonneg (Int.le_of_lt hM))
  have hn_nonneg : 0 ≤ n := Int.le_trans h4M4_nonneg hM4
  have hq_nonneg : 0 ≤ q := Int.fdiv_nonneg hn_nonneg (Int.le_of_lt hMa_pos)
  -- ===== Upper bound: n < (M*a + q + 1)² =====
  have upper : n < (M * a + q + 1)^2 := by
    -- floor-div upper: n < (q+1)·4Ma
    have hq_ub : n < (q + 1) * (4 * M * a) := Int.lt_fdiv_add_one_mul_self n hMa_pos
    -- (q+1)·4Ma ≤ (Ma+q+1)² by AM–GM (4xy ≤ (x+y)²)
    have hle : (q + 1) * (4 * M * a) ≤ (M * a + q + 1)^2 := by
      have := four_mul_le_add_sq (M * a) (q + 1)
      grind only
    exact Int.lt_of_lt_of_le hq_ub hle
  -- ===== Lower bound: (M*a + q - 1)² < n =====
  have lower : (M * a + q - 1)^2 < n := by
    -- Chain: 4M² ≤ 4Ma ≤ 4M²a² + 4Maq ≤ 4M²a² + n
    have key1 : 4 * M^2 ≤ 4 * M * a := by
      -- 4Ma - 4M² = 4M(a - M) ≥ 0
      have factor : (4 * M) * (a - M) = 4 * M * a - 4 * M^2 := by grind only
      exact Int.sub_nonneg.mp (factor ▸ Int.mul_nonneg (by omega) (by omega))
    have key2 : 4 * M * a ≤ 4 * M^2 * a^2 + 4 * M * a * q := by
      -- difference = 4Ma(Ma + q - 1) ≥ 0
      have factor : (4 * M * a) * (M * a + q - 1)
          = (4 * M^2 * a^2 + 4 * M * a * q) - 4 * M * a := by grind only
      exact Int.sub_nonneg.mp (factor ▸ Int.mul_nonneg (Int.le_of_lt hMa_pos) (by omega))
    have key3 : 4 * M^2 * a^2 + 4 * M * a * q ≤ 4 * M^2 * a^2 + n := by
      -- 4Maq ≤ n (floor div); add 4M²a² to both sides
      have hqm : 4 * M * a * q ≤ n := by
        exact Int.mul_fdiv_self_le hMa_pos
      exact Int.add_le_add_left hqm (4 * M^2 * a^2)
    have hsq := square_squeeze key1 key2 key3
    -- d_large: n < 4M²a² + 4M² + 8M²a  (rearranged from n_upper)
    have d_large : n < 4 * M^2 * a^2 + 4 * M^2 + 8 * M^2 * a := by
      have := n_upper hM ha_hi
      grind only
    -- d_small: 4M²a² + 4M² < n + 8M²a  (rearranged from n_lower; needs 0 < M²)
    have d_small : 4 * M^2 * a^2 + 4 * M^2 < n + 8 * M^2 * a := by
      have := n_lower hM ha_lo
      have hM2 : 0 < M^2 := Int.pow_pos hM
      grind only
    have hclose := close_to d_large d_small
    -- The two inequalities provide nonneg "gaps". Their sum equals
    -- `n*(4Ma)² - (M*a + q - 1)²*(4Ma)²` as a polynomial identity (by `grind`),
    -- which gives `(M*a + q - 1)²·(4Ma)² < n·(4Ma)²`.
    have h_sq_gap : 0 ≤
        ((4 * M^2)^2 + (4 * M^2 * a^2 + n)^2
            + 2 * (4 * M * a) * (4 * M^2 * a^2 + 4 * M * a * q))
          - ((4 * M * a)^2 + (4 * M^2 * a^2 + 4 * M * a * q)^2
            + 2 * (4 * M^2) * (4 * M^2 * a^2 + n)) := Int.sub_nonneg.mpr hsq
    have h_close_gap : 0 <
        ((8 * M^2 * a)^2 + 2 * n * (4 * M^2 * a^2 + 4 * M^2))
          - (n^2 + (4 * M^2 * a^2 + 4 * M^2)^2) := Int.sub_pos.mpr hclose
    have h_identity :
        n * (4 * M * a)^2 - (M * a + q - 1)^2 * (4 * M * a)^2 =
          (((4 * M^2)^2 + (4 * M^2 * a^2 + n)^2
              + 2 * (4 * M * a) * (4 * M^2 * a^2 + 4 * M * a * q))
            - ((4 * M * a)^2 + (4 * M^2 * a^2 + 4 * M * a * q)^2
              + 2 * (4 * M^2) * (4 * M^2 * a^2 + n)))
          + (((8 * M^2 * a)^2 + 2 * n * (4 * M^2 * a^2 + 4 * M^2))
            - (n^2 + (4 * M^2 * a^2 + 4 * M^2)^2)) := by grind only
    have h_squared : (M * a + q - 1)^2 * (4 * M * a)^2 < n * (4 * M * a)^2 :=
      Int.sub_pos.mp (h_identity.symm ▸ Int.add_pos_of_nonneg_of_pos h_sq_gap h_close_gap)
    -- Cancel (4Ma)²
    exact Int.lt_of_mul_lt_mul_right h_squared (Int.sq_nonneg _)
  -- Convert the `^2`-form bounds back to the multiplicative `isNearSquareRoot`.
  exact ⟨by grind only, by grind only⟩
