/-
Supporting lemmas for the isqrt proof that are *not* about our Python primitives — the kind of
general `Int` / `Nat` facts Mathlib would supply, reproduced here for the Mathlib-free build.

Most concern `Int.fdiv` (floor division): many are thin wrappers around existing `Int.ediv`
lemmas, using `Int.fdiv_eq_ediv_of_nonneg` to convert when the divisor is nonneg, stated for
`Int.fdiv` so downstream proofs use them directly after unfolding `pyFloordiv` / `pyRshift`. The
file also collects the stray `Nat` facts (e.g. `Nat.log2`) the proofs need but core does not give.
-/

module

public section

/-! ## Basic ordering lemmas for `Int.fdiv` -/

/-- `y ≤ x.fdiv k ↔ y * k ≤ x` when `0 < k`. -/
theorem Int.le_fdiv_iff_mul_le {x y k : Int} (hk : 0 < k) :
    y ≤ x.fdiv k ↔ y * k ≤ x := by
  rw [Int.fdiv_eq_ediv_of_nonneg x (Int.le_of_lt hk)]
  exact Int.le_ediv_iff_mul_le hk

/-- `x.fdiv k < y ↔ x < y * k` when `0 < k`. -/
theorem Int.fdiv_lt_iff_lt_mul {x y k : Int} (hk : 0 < k) :
    x.fdiv k < y ↔ x < y * k := by
  rw [Int.fdiv_eq_ediv_of_nonneg x (Int.le_of_lt hk)]
  exact Int.ediv_lt_iff_lt_mul hk

/-! ## Nested floor division -/

/-- Nested floor division collapses to division by the product:
`⌊⌊a / b⌋ / c⌋ = ⌊a / (b * c)⌋` for nonneg divisors `b`, `c`. For nonneg `b`, `c`
each `fdiv` agrees with `Int.ediv`, and core's `Int.ediv_ediv_of_nonneg` supplies the
`ediv` identity. The recursion's `c ↦ c // 2` step and the iterative loop's
scaler division both consume this. -/
theorem Int.fdiv_fdiv_eq_fdiv_mul (a : Int) {b c : Int} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a.fdiv b).fdiv c = a.fdiv (b * c) := by
  rw [Int.fdiv_eq_ediv_of_nonneg a hb, Int.fdiv_eq_ediv_of_nonneg _ hc,
      Int.ediv_ediv_of_nonneg hb, Int.fdiv_eq_ediv_of_nonneg a (Int.mul_nonneg hb hc)]

/-! ## Shift ↔ floor division -/

/-- The arithmetic right shift is floor division by a power of two: `n >>> k = ⌊n / 2^k⌋`.
Core's `Int.shiftRight_eq_div_pow` gives `n / 2^k` (Euclidean division), which is `Int.fdiv` for
the nonneg divisor `2^k`. The bridge that lets `SizedProblem`'s shift-form operations meet the
`Int.fdiv` size-condition and key-lemma theory below them. -/
theorem Int.shiftRight_eq_fdiv (n : Int) (k : Nat) : n >>> k = n.fdiv (2 ^ k) := by
  have h2 : (0 : Int) ≤ 2 ^ k := Int.pow_nonneg (by omega)
  rw [Int.shiftRight_eq_div_pow, Int.fdiv_eq_ediv_of_nonneg n h2]
  norm_cast

/-! ## Shift inequalities -/

/-- A nonneg integer is at most its left shift: `n ≤ n <<< s`. The left-shift companion to core's
`Int.le_shiftRight_of_nonneg` (`0 ≤ n → 0 ≤ n >>> s`); core has the right-shift facts but not this
one. For nonneg `n` it reduces to the `Nat` fact `Nat.le_shiftLeft` by pushing the cast through the
shift (`natCast_shiftLeft`). -/
theorem Int.le_shiftLeft_of_nonneg {n : Int} {s : Nat} (h : 0 ≤ n) : n ≤ n <<< s := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
  exact_mod_cast Nat.le_shiftLeft

/-! ## Int ↔ Nat bridging -/

/-- For nonneg `x` and nonneg `y`, `Int.fdiv` and `Nat` division agree
under `toNat`. -/
theorem Int.toNat_fdiv_of_nonneg {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x.fdiv y).toNat = x.toNat / y.toNat := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hy
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg b)]
  rfl

/-- `Int.fdiv` of two `Nat`-casts is the cast of the `Nat` quotient:
`(↑a).fdiv ↑b = ↑(a / b)`. The value-level companion to `Int.toNat_fdiv_of_nonneg`;
once a divisor is exposed as a `Nat`-cast, this collapses the `fdiv` into a single
`Nat` division, which is the bridge the size-condition and bit-length proofs lean on. -/
theorem Int.fdiv_natCast_natCast (a b : Nat) : (↑a : Int).fdiv ↑b = ↑(a / b) := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg b)]
  rfl

/-- `⌊(c - 1) / 2⌋.toNat = (c - 1) / 2` for `0 < c`: floor-halving the integer `↑c - 1`
and taking `toNat` agrees with `Nat` division of the predecessor. The Int↔Nat bridge the
size-condition proofs use for the recursion's `k = (c - 1) // 2`. The `0 < c` hypothesis
keeps `↑c - 1` (Int) in step with `c - 1` (truncating Nat subtraction). -/
theorem Int.toNat_fdiv_pred_two {c : Nat} (hc : 0 < c) :
    (Int.fdiv (↑c - 1 : Int) 2).toNat = (c - 1) / 2 := by
  rw [show ((↑c : Int) - 1) = ((c - 1 : Nat) : Int) from by omega,
      show ((2 : Int)) = ((2 : Nat) : Int) from rfl,
      Int.toNat_fdiv_of_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)]
  simp

/-! ## Nat.log2 under right shifts -/

/-- A positive `n` stays positive after a right shift by at most its bit length: `0 < n >>> k`
when `k ≤ n.log2` (equivalently `2^k ≤ n`). -/
theorem Nat.shiftRight_pos {n k : Nat} (hn : 0 < n) (hk : k ≤ n.log2) : 0 < n >>> k := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_pos ((Nat.le_log2 (Nat.ne_of_gt hn)).mp hk) (Nat.pow_pos (by decide))

/-- Right-shifting drops exactly `k` from the base-2 log: `(n >>> k).log2 = n.log2 - k`, for all
`n` and `k` (the `log2`/right-shift analogue of Mathlib's `Nat.log_div_base_pow`). The arithmetic
core of the size condition's descent (`size_condition_at_depth`): shifting right by `k` lowers `n`'s
bit length by exactly `k` (and to `0` once `k` exceeds it, where both sides vanish). -/
theorem Nat.log2_shiftRight (n k : Nat) : (n >>> k).log2 = n.log2 - k := by
  rw [Nat.shiftRight_eq_div_pow]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnne : n ≠ 0 := by omega
    rcases Nat.lt_or_ge n.log2 k with hk | hk
    · -- `k` past the bit length: `n < 2^k`, so `n / 2^k = 0` and `n.log2 - k = 0`.
      rw [Nat.div_eq_of_lt ((Nat.log2_lt hnne).mp hk), show n.log2 - k = 0 from by omega]; simp
    · -- `k ≤ n.log2`: `2^k` still fits, so the bit length drops by exactly `k`.
      have h2k : 0 < 2 ^ k := Nat.pow_pos (by decide)
      have hlo : 2 ^ k ≤ n := (Nat.le_log2 hnne).mp hk
      have hdiv_pos : 0 < n / 2 ^ k := Nat.div_pos hlo h2k
      rw [Nat.log2_eq_iff (by omega)]
      refine ⟨?_, ?_⟩
      · rw [Nat.le_div_iff_mul_le h2k, ← Nat.pow_add, Nat.sub_add_cancel hk]
        exact Nat.log2_self_le hnne
      · rw [Nat.div_lt_iff_lt_mul h2k, ← Nat.pow_add,
            show n.log2 - k + 1 + k = n.log2 + 1 from by omega]
        exact Nat.lt_log2_self

end
