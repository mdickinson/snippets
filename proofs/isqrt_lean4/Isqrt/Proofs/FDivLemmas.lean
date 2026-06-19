/-
Lemmas about `Int.fdiv` (floor division) needed for the isqrt proof.

Many of these are thin wrappers around existing `Int.ediv` lemmas,
using `Int.fdiv_eq_ediv_of_nonneg` to convert when the divisor is
nonneg. We state them for `Int.fdiv` so that proofs downstream can
use them directly after unfolding `pyFloordiv` / `pyRshift`.
-/

import Mathlib.Tactic.Linarith

/-! ## Basic ordering lemmas for `Int.fdiv` -/

/-- `(x.fdiv k) * k ≤ x` when `0 < k`. Swapped-argument version of
`Int.mul_fdiv_self_le`. -/
theorem Int.fdiv_mul_le_self {x k : ℤ} (h : 0 < k) : x.fdiv k * k ≤ x := by
  rw [Int.mul_comm]
  exact Int.mul_fdiv_self_le h

/-- `y ≤ x.fdiv k ↔ y * k ≤ x` when `0 < k`. -/
theorem Int.le_fdiv_iff_mul_le {x y k : ℤ} (hk : 0 < k) :
    y ≤ x.fdiv k ↔ y * k ≤ x := by
  rw [Int.fdiv_eq_ediv_of_nonneg x hk.le]
  exact Int.le_ediv_iff_mul_le hk

/-- `x.fdiv k < y ↔ x < y * k` when `0 < k`. -/
theorem Int.fdiv_lt_iff_lt_mul {x y k : ℤ} (hk : 0 < k) :
    x.fdiv k < y ↔ x < y * k := by
  rw [Int.fdiv_eq_ediv_of_nonneg x hk.le]
  exact Int.ediv_lt_iff_lt_mul hk

/-! ## ℤ ↔ ℕ bridging -/

/-- For nonneg `x` and nonneg `y`, `Int.fdiv` and `Nat` division agree
under `toNat`. -/
theorem Int.toNat_fdiv_of_nonneg {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x.fdiv y).toNat = x.toNat / y.toNat := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hy
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg b)]
  rfl

/-- `Int.fdiv` of two `ℕ`-casts is the cast of the `Nat` quotient:
`(↑a).fdiv ↑b = ↑(a / b)`. The value-level companion to `Int.toNat_fdiv_of_nonneg`;
once a divisor is exposed as a `ℕ`-cast, this collapses the `fdiv` into a single
`Nat` division, which is the bridge the size-condition and bit-length proofs lean on. -/
theorem Int.fdiv_natCast_natCast (a b : ℕ) : (↑a : ℤ).fdiv ↑b = ↑(a / b) := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg b)]
  rfl

/-- `⌊(c - 1) / 2⌋.toNat = (c - 1) / 2` for `0 < c`: floor-halving the integer `↑c - 1`
and taking `toNat` agrees with `Nat` division of the predecessor. The ℤ↔ℕ bridge the
size-condition proofs use for the recursion's `k = (c - 1) // 2`. The `0 < c` hypothesis
keeps `↑c - 1` (ℤ) in step with `c - 1` (truncating ℕ subtraction). -/
theorem Int.toNat_fdiv_pred_two {c : ℕ} (hc : 0 < c) :
    (Int.fdiv (↑c - 1 : ℤ) 2).toNat = (c - 1) / 2 := by
  rw [show ((↑c : ℤ) - 1) = ((c - 1 : ℕ) : ℤ) from by omega,
      show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl,
      Int.toNat_fdiv_of_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)]
  simp
