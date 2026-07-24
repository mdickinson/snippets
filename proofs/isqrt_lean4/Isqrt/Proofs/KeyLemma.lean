module

public import Isqrt.Definitions.Specification

/-!
The isqrt correctness proof's pure-integer mathematics: near-square-root theory, the
Newton-step key lemma, and the closing correction from near square root to `⌊√n⌋`.

The **near square root** predicate `isNearSquareRoot n a` asserts `0 < a` and
`(a-1)² < n < (a+1)²`; for positive `n`, `a` is then `⌊√n⌋` or `⌈√n⌉`. The key combining step,
`key_lemma`, lifts a near square root of a quotient of `n` to a near square root of `n` —
one Newton (Heron) iteration:

    given positive integers `n`, `M`, `a` with `4M⁴ ≤ n`, if `a` is a near square root of
    `⌊n/4M²⌋`, then `Ma + ⌊n/4Ma⌋` is a near square root of `n`.

## Proof sketch for `key_lemma`

Write `q = ⌊n/4Ma⌋`; the goal is `(Ma+q-1)² < n < (Ma+q+1)²`. It rests on four facts:

    (L)  4M²(a-1)² < n           `a` a near square root of `⌊n/4M²⌋`, lower half
    (U)  n < 4M²(a+1)²           `a` a near square root of `⌊n/4M²⌋`, upper half
    (F)  4Ma·q ≤ n < 4Ma(q+1)    the two floor bounds on `q = ⌊n/4Ma⌋`
    and  M ≤ a                   (from `4M⁴ ≤ n` together with (U)).

Lower bound (the numbers match the `have`s in the code):

    (1)  (4M²a²+n-4M²)² < 16M²a²n              from (L) and (U)                     [hnewton]
    (2)  4M² ≤ 4Ma ≤ 4M²a²+4Maq ≤ 4M²a²+n      from `M ≤ a`, `1 ≤ Ma`, and (F)
    (3)  (4M²a²+4Maq-4Ma)² ≤ (4M²a²+n-4M²)²    from (2): if `a ≤ b ≤ c ≤ d` then    [hsq]
                                                `(c-b)² ≤ (d-a)²`

The left side of (3) is `(4Ma(Ma+q-1))²`, so chaining (3) into (1) gives
`(4Ma(Ma+q-1))² < 16M²a²n = (4Ma)²·n`; cancelling `(4Ma)²` leaves `(Ma+q-1)² < n`.

Upper bound:  n < 4Ma(q+1) ≤ (Ma+q+1)²          from (F), then AM–GM `4xy ≤ (x+y)²`.
-/

/-! ## Algebraic helpers -/

/-- Squaring is squaring. -/
theorem mul_self_eq_sq {x : Int} : x * x = x ^ 2 := by grind only

/-- `x ≤ y` implies `x² ≤ y²`, provided `x` is nonnegative. -/
theorem sq_le_sq_of_le {x y : Int} (h : 0 ≤ x) (h' : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  grind only [Int.mul_nonneg (by omega : 0 ≤ y - x) (by omega : 0 ≤ y + x)]

/-- `x² < y²` implies `x < y`, provided `y` is nonnegative. -/
theorem lt_of_sq_lt_sq {x y : Int} (hy : 0 ≤ y) (h : x ^ 2 < y ^ 2) : x < y := by
  rw [← Int.not_le]; intro hyx; grind only [sq_le_sq_of_le hy hyx]

/-- The AM–GM inequality for two integers: `4xy ≤ (x+y)²` (equivalently `0 ≤ (x−y)²`). -/
theorem four_mul_le_add_sq (x y : Int) : 4 * x * y ≤ (x + y) ^ 2 := by
  grind only [Int.sq_nonneg (x - y)]

/-! ## Suitable scalers -/

/-- `M` is a *suitable scaler* for `n`: `0 < M` and `4M⁴ ≤ n`. -/
@[expose] public def isSuitableScaler (n M : Int) := 0 < M ∧ 4 * M^4 ≤ n

/-! ## The key lemma -/

/-- If `M` is a suitable scaler for `n` and `a` is a near square root of `⌊n / 4M²⌋`, then
`Ma + ⌊n / 4Ma⌋` is a near square root of `n`. -/
public theorem key_lemma {n M a : Int}
    (hM_scaler : isSuitableScaler n M)
    (h_near : isNearSquareRoot (n / (4 * M^2)) a) :
    isNearSquareRoot n (M * a + n / (4 * M * a)) := by
  -- Unpack hypotheses.
  obtain ⟨hM, hM4⟩ := hM_scaler
  obtain ⟨ha, ha_lo, ha_hi⟩ := h_near
  -- Bounds (L): `4M²(a-1)² < n` and (U): `n < 4M²(a+1)²`.
  have h4M2_pos : 0 < 4 * M^2 := Int.mul_pos (by decide) (Int.pow_pos hM)
  have hL : 4 * M^2 * (a - 1)^2 < n := by
    grind only [Int.mul_le_of_le_ediv h4M2_pos (Int.add_one_le_of_lt ha_lo)]
  have hU : n < 4 * M^2 * (a + 1)^2 := by
    grind only [Int.lt_mul_of_ediv_lt h4M2_pos ha_hi]
  -- `M ≤ a` follows from `4M⁴ ≤ n` and (U).
  have hM_le_a : M ≤ a := by
    have : M^2 ≤ n / (4 * M^2) := Int.le_ediv_of_mul_le h4M2_pos (by grind only)
    grind only [lt_of_sq_lt_sq (by omega) (Int.lt_of_le_of_lt this (mul_self_eq_sq ▸ ha_hi))]
  -- Abbreviate n / 4Ma to q; q satisfies `4Maq ≤ n < 4Ma(q+1)`.
  let q := n / (4 * M * a)
  have h4Ma_pos : 0 < 4 * M * a := Int.mul_pos (Int.mul_pos (by decide) hM) ha
  have hn_pos : 0 < n := Int.lt_of_lt_of_le (Int.mul_pos (by decide) (Int.pow_pos hM)) hM4
  have hq_nonneg : 0 ≤ q := Int.ediv_nonneg (Int.le_of_lt hn_pos) (Int.le_of_lt h4Ma_pos)
  have hq_lb : 4 * M * a * q ≤ n := Int.mul_ediv_self_le (Int.ne_of_gt h4Ma_pos)
  have hq_ub : n < 4 * M * a * q + 4 * M * a := Int.lt_mul_ediv_self_add h4Ma_pos
  -- Positivity: 0 < Ma + q
  have pos : 0 < M * a + q := by grind only
  -- Lower bound: (Ma + q - 1)² < n
  have lower : (M * a + q - 1) * (M * a + q - 1) < n := by
    -- (1)  16M²a²n − (4M²a²+n−4M²)² is exactly the (L)-gap times the (U)-gap, hence positive.
    have hgap : 0 < (n - 4 * M^2 * (a - 1)^2) * (4 * M^2 * (a + 1)^2 - n) :=
      Int.mul_pos (Int.sub_pos.mpr hL) (Int.sub_pos.mpr hU)
    have hnewton : (4 * M^2 * a^2 + n - 4 * M^2)^2 < 16 * M^2 * a^2 * n := by grind only
    -- (2)  the chain 4M² ≤ 4Ma ≤ 4M²a²+4Maq ≤ 4M²a²+n, via `h4M2` (`M ≤ a`) and `hq_lb` (floor).
    have h4M2 : 4 * M^2 ≤ 4 * M * a := by
      grind only [Int.mul_nonneg (by omega : 0 ≤ 4 * M) (by omega : 0 ≤ a - M)]
    -- The inner gap of (2) is `V = 4Ma(Ma+q−1) = 4M²a²+4Maq−4Ma`, with `0 ≤ V` (as `1 ≤ Ma`)
    -- and `V ≤ 4M²a²+n−4M²` (the outer gap); squaring these bounds is step (3), `hsq`.
    have hVnonneg : 0 ≤ 4 * M * a * (M * a + q - 1) :=
      Int.mul_nonneg (Int.le_of_lt h4Ma_pos) (by omega)
    have hVY : 4 * M * a * (M * a + q - 1) ≤ 4 * M^2 * a^2 + n - 4 * M^2 := by grind only
    -- (3)
    have hsq : (4 * M * a * (M * a + q - 1))^2 ≤ (4 * M^2 * a^2 + n - 4 * M^2)^2 :=
      sq_le_sq_of_le hVnonneg hVY
    -- Chain (3) into (1), then cancel (4Ma)² (= 16M²a²): `(Ma+q−1)²·(4Ma)² < n·(4Ma)²`.
    have hfinal : (M * a + q - 1) * (M * a + q - 1) * (4 * M * a)^2 < n * (4 * M * a)^2 := by
      grind only
    exact Int.lt_of_mul_lt_mul_right hfinal (Int.sq_nonneg (4 * M * a))
  -- Upper bound: n < 4Ma(q + 1) ≤ (Ma + q + 1)²
  have upper : n < (M * a + q + 1) * (M * a + q + 1) :=
    Int.lt_of_lt_of_le hq_ub (by grind only [four_mul_le_add_sq (M * a) (q + 1)])
  -- Convert the `^2`-form bounds back to the multiplicative `isNearSquareRoot`.
  exact ⟨pos, lower, upper⟩

/-! ## The closing correction -/

/-- Turn a near square root into the integer square root: subtract one exactly when `n < a*a`. -/
public theorem isIntegerSquareRoot_of_isNearSquareRoot {n a : Int} (h : isNearSquareRoot n a) :
    isIntegerSquareRoot n (if n < a * a then a - 1 else a) := by
  obtain ⟨ha_pos, h_lo, h_hi⟩ := h
  by_cases h_lt : n < a * a
  · simp only [h_lt, ↓reduceIte]
    exact ⟨by omega, Int.le_of_lt h_lo, by grind only⟩
  · simp only [h_lt, ↓reduceIte]
    exact ⟨Int.le_of_lt ha_pos, Int.not_lt.mp h_lt, h_hi⟩
