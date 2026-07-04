/-
The isqrt correctness proof's pure-integer mathematics: near-square-root theory and the
Newton-step key lemma. It is all general `Int` arithmetic — the bit-level encoding the
algorithm divides by (shifts, powers of two) lives in `Isqrt.Proofs.SizedProblem`.

The **near square root** predicate `isNearSquareRoot` (`(a-1)² < n < (a+1)²`; for positive `n`,
`a` is `⌊√n⌋` or `⌈√n⌉`) is defined in `Isqrt.Definitions.Specification`. The key combining
step, `key_isqrt_lemma`, lifts a near square root of a quotient of `n` to a near square root of
`n` — one Newton (Heron) iteration:

    given positive integers `n`, `M`, `a` with `4M⁴ ≤ n`, if `a` is a near square root of
    `⌊n/4M²⌋`, then `Ma + ⌊n/4Ma⌋` is a near square root of `n`.

## Proof sketch for `key_isqrt_lemma`

Write `q = ⌊n/4Ma⌋`; the goal is `(Ma+q-1)² < n < (Ma+q+1)²`. It rests on four facts:

    (L)  4M²(a-1)² < n           `a` a near square root of `⌊n/4M²⌋`, lower half
    (U)  n < 4M²(a+1)²           `a` a near square root of `⌊n/4M²⌋`, upper half
    (F)  4Ma·q ≤ n < 4Ma(q+1)    the two floor bounds on `q = ⌊n/4Ma⌋`
    and  M ≤ a                   (from `4M⁴ ≤ n` together with (U)).

Upper bound:  n < 4Ma(q+1) ≤ (Ma+q+1)²          from (F), then AM–GM `4xy ≤ (x+y)²`.

Lower bound (the numbers match the `have`s in the code):

    (1)  (4M²a²+n-4M²)² < 16M²a²n               from (L) and (U)                    [hnewton]
    (2)  4M² ≤ 4Ma ≤ 4M²a²+4Maq ≤ 4M²a²+n      from `M ≤ a`, `1 ≤ Ma`, and (F)
    (3)  (4M²a²+4Maq-4Ma)² ≤ (4M²a²+n-4M²)²    from (2): if `a ≤ b ≤ c ≤ d` then    [hsq]
                                                `(c-b)² ≤ (d-a)²`

The left side of (3) is `(4Ma(Ma+q-1))²`, so chaining (3) into (1) gives
`(4Ma(Ma+q-1))² < 16M²a²n = (4Ma)²·n`; cancelling `(4Ma)²` leaves `(Ma+q-1)² < n`.
-/

module

public import Isqrt.Definitions.Specification

/-! ## Positivity -/

/-- A near square root is positive. -/
public theorem isNearSquareRoot.pos {n a : Int} (h : isNearSquareRoot n a) : 0 < a := by
  obtain ⟨h_lo, h_hi⟩ := h
  grind only

/-! ## Algebraic helpers -/

/-- For integers, `x² < y²` with `0 ≤ y` gives `x < y`. -/
theorem lt_of_sq_lt_sq {x y : Int} (hy : 0 ≤ y) (h : x ^ 2 < y ^ 2) : x < y := by
  obtain hlt | hle := Int.lt_or_le x y
  · exact hlt
  · -- `y ≤ x` with `0 ≤ y` forces `y² ≤ x²`, contradicting `h`.
    grind only [Int.mul_nonneg (by omega : 0 ≤ x - y) (by omega : 0 ≤ x + y)]

/-- The AM–GM inequality for two integers: `4xy ≤ (x+y)²` (equivalently `0 ≤ (x−y)²`). -/
theorem four_mul_le_add_sq (x y : Int) : 4 * x * y ≤ (x + y) ^ 2 := by
  grind only [Int.sq_nonneg (x - y)]

/-! ## Sub-lemmas about the setup -/

/-- `M ≤ a`, given `4M⁴ ≤ n` and `n/(4M²) < (a+1)²`. -/
theorem M_le_a {n M a : Int}
    (hM : 0 < M) (ha : 0 < a) (hM4 : 4 * M^4 ≤ n)
    (ha_hi : n / (4 * M^2) < (a + 1)^2) :
    M ≤ a := by
  have hdenom : 0 < 4 * M^2 := Int.mul_pos (by decide) (Int.pow_pos hM)
  have h1 : M^2 ≤ n / (4 * M^2) := by
    rw [Int.le_ediv_iff_mul_le hdenom, show M^2 * (4 * M^2) = 4 * M^4 from by grind only]
    exact hM4
  have h2 : M^2 < (a + 1)^2 := Int.lt_of_le_of_lt h1 ha_hi
  have : M < a + 1 := lt_of_sq_lt_sq (by omega) h2
  omega

/-- Bound (U): `n < 4M²(a+1)²` (equivalently `√n < 2M(a+1)`). -/
theorem n_upper {n M a : Int} (hM : 0 < M)
    (ha_hi : n / (4 * M^2) < (a + 1)^2) :
    n < 4 * M^2 * (a + 1)^2 := by
  have hdenom : 0 < 4 * M^2 := Int.mul_pos (by decide) (Int.pow_pos hM)
  have := (Int.ediv_lt_iff_lt_mul hdenom).mp ha_hi
  grind only

/-- Bound (L): `4M²(a-1)² < n` (equivalently `2M(a-1) < √n`). -/
theorem n_lower {n M a : Int} (hM : 0 < M)
    (ha_lo : (a - 1)^2 < n / (4 * M^2)) :
    4 * M^2 * (a - 1)^2 < n := by
  have hdenom : 0 < 4 * M^2 := Int.mul_pos (by decide) (Int.pow_pos hM)
  have h1 : ((a - 1)^2 + 1) * (4 * M^2) ≤ n := by
    rw [← Int.le_ediv_iff_mul_le hdenom]; omega
  grind only

/-! ## Suitable scalers -/

/-- `M` is a *suitable scaler* for `n`: `0 < M` and `4M⁴ ≤ n`. -/
@[expose] public def isSuitableScaler (n M : Int) : Prop := 0 < M ∧ 4 * M^4 ≤ n

/-! ## The key lemma -/

/-- If `M` is a suitable scaler for `n` and `a` is a near square root of `⌊n / 4M²⌋`, then
`Ma + ⌊n / 4Ma⌋` is a near square root of `n`. -/
public theorem key_isqrt_lemma {n M a : Int}
    (hM_scaler : isSuitableScaler n M)
    (h_near : isNearSquareRoot (n / (4 * M^2)) a) :
    isNearSquareRoot n (M * a + n / (4 * M * a)) := by
  obtain ⟨hM, hM4⟩ := hM_scaler
  have ha : 0 < a := h_near.pos
  obtain ⟨ha_lo, ha_hi⟩ := h_near
  -- `isNearSquareRoot` is multiplicative; recover the `^2` shape the algebra uses.
  rw [show (a - 1) * (a - 1) = (a - 1) ^ 2 from by grind only] at ha_lo
  rw [show (a + 1) * (a + 1) = (a + 1) ^ 2 from by grind only] at ha_hi
  -- The near-square-root hypothesis, cleared of the floor and the `4M²`, gives bounds (U)/(L);
  -- `M ≤ a` follows from `4M⁴ ≤ n` and (U). (See the proof sketch at the top of the file.)
  have hU : n < 4 * M^2 * (a + 1)^2 := n_upper hM ha_hi
  have hL : 4 * M^2 * (a - 1)^2 < n := n_lower hM ha_lo
  have hM_le_a : M ≤ a := M_le_a hM ha hM4 ha_hi
  let q := n / (4 * M * a)
  have hMa_pos : 0 < 4 * M * a := Int.mul_pos (Int.mul_pos (by decide) hM) ha
  have hMa_one : 1 ≤ M * a := by have := Int.mul_pos hM ha; omega
  have h4M4_nonneg : 0 ≤ 4 * M^4 :=
    Int.mul_nonneg (by decide) (Int.pow_nonneg (Int.le_of_lt hM))
  have hn_nonneg : 0 ≤ n := Int.le_trans h4M4_nonneg hM4
  have hq_nonneg : 0 ≤ q := Int.ediv_nonneg hn_nonneg (Int.le_of_lt hMa_pos)
  -- ===== Upper bound: n < 4Ma(q+1) ≤ (Ma+q+1)² =====
  have upper : n < (M * a + q + 1)^2 := by
    have hq_ub : n < (q + 1) * (4 * M * a) := Int.lt_ediv_add_one_mul_self n hMa_pos
    have hle : (q + 1) * (4 * M * a) ≤ (M * a + q + 1)^2 := by
      have := four_mul_le_add_sq (M * a) (q + 1)
      grind only
    exact Int.lt_of_lt_of_le hq_ub hle
  -- ===== Lower bound: (Ma + q - 1)² < n =====
  have lower : (M * a + q - 1)^2 < n := by
    -- (1)  16M²a²n − (4M²a²+n−4M²)² factors as the product of the (L) and (U) gaps, so is > 0.
    have hnewton : (4 * M^2 * a^2 + n - 4 * M^2)^2 < 16 * M^2 * a^2 * n := by
      grind only [Int.mul_pos (Int.sub_pos.mpr hL) (Int.sub_pos.mpr hU)]
    -- (2)  the chain 4M² ≤ 4Ma ≤ 4M²a²+4Maq ≤ 4M²a²+n, via `h4M2` (`M ≤ a`) and `h4Maq` (floor).
    have h4M2 : 4 * M^2 ≤ 4 * M * a := by
      grind only [Int.mul_nonneg (by omega : 0 ≤ 4 * M) (by omega : 0 ≤ a - M)]
    have h4Maq : 4 * M * a * q ≤ n := Int.mul_ediv_self_le (Int.ne_of_gt hMa_pos)
    -- The inner gap of (2) is `V = 4Ma(Ma+q−1) = 4M²a²+4Maq−4Ma`, with `0 ≤ V` (as `1 ≤ Ma`)
    -- and `V ≤ 4M²a²+n−4M²` (the outer gap); squaring these bounds is step (3), `hsq`.
    have hVnonneg : 0 ≤ 4 * M * a * (M * a + q - 1) :=
      Int.mul_nonneg (Int.le_of_lt hMa_pos) (by omega)
    have hVY : 4 * M * a * (M * a + q - 1) ≤ 4 * M^2 * a^2 + n - 4 * M^2 := by
      grind only
    -- (3)
    have hsq : (4 * M * a * (M * a + q - 1))^2 ≤ (4 * M^2 * a^2 + n - 4 * M^2)^2 := by
      grind only [Int.mul_nonneg
        (by omega : 0 ≤ (4 * M^2 * a^2 + n - 4 * M^2) - 4 * M * a * (M * a + q - 1))
        (by omega : 0 ≤ (4 * M^2 * a^2 + n - 4 * M^2) + 4 * M * a * (M * a + q - 1))]
    -- Chain (3) into (1), then cancel (4Ma)² (= 16M²a²): `(Ma+q−1)²·(4Ma)² < n·(4Ma)²`.
    have hfinal : (M * a + q - 1)^2 * (4 * M * a)^2 < n * (4 * M * a)^2 := by grind only
    exact Int.lt_of_mul_lt_mul_right hfinal (Int.sq_nonneg _)
  -- Convert the `^2`-form bounds back to the multiplicative `isNearSquareRoot`.
  exact ⟨by grind only, by grind only⟩
