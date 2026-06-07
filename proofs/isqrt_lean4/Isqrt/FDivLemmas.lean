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

/-- Floor-dividing a nonneg integer by a positive integer cannot increase it. -/
theorem Int.fdiv_le_self_of_nonneg {x k : ℤ} (hx : 0 ≤ x) (hk : 0 < k) :
    x.fdiv k ≤ x := by
  have h0 : 0 ≤ x.fdiv k := Int.fdiv_nonneg hx hk.le
  have h1 : x.fdiv k * k ≤ x := Int.fdiv_mul_le_self hk
  nlinarith [h1, mul_nonneg h0 (show (0 : ℤ) ≤ k - 1 by omega)]

/-- `y ≤ x.fdiv k ↔ y * k ≤ x` when `0 < k`. -/
theorem Int.le_fdiv_iff_mul_le {x y k : ℤ} (hk : 0 < k) :
    y ≤ x.fdiv k ↔ y * k ≤ x := by
  rw [Int.fdiv_eq_ediv_of_nonneg x (Int.le_of_lt hk)]
  exact Int.le_ediv_iff_mul_le hk

/-- `x.fdiv k < y ↔ x < y * k` when `0 < k`. -/
theorem Int.fdiv_lt_iff_lt_mul {x y k : ℤ} (hk : 0 < k) :
    x.fdiv k < y ↔ x < y * k := by
  rw [Int.fdiv_eq_ediv_of_nonneg x (Int.le_of_lt hk)]
  exact Int.ediv_lt_iff_lt_mul hk

/-- `x.fdiv k ≤ y ↔ x < y * k + k` when `0 < k`. -/
theorem Int.fdiv_le_iff_lt_mul_add {x y k : ℤ} (hk : 0 < k) :
    x.fdiv k ≤ y ↔ x < y * k + k := by
  rw [Int.fdiv_eq_ediv_of_nonneg x (Int.le_of_lt hk)]
  exact Int.ediv_le_iff_le_mul hk

/-- `x < (x.fdiv k + 1) * k` when `0 < k`. The next multiple of `k` above
`x.fdiv k * k` is strictly greater than `x`. -/
theorem Int.lt_fdiv_add_one_mul {x k : ℤ} (hk : 0 < k) :
    x < (x.fdiv k + 1) * k := by
  rw [add_mul, one_mul]
  exact (Int.fdiv_le_iff_lt_mul_add hk).mp le_rfl

/-! ## ℤ ↔ ℕ bridging -/

/-- For nonneg `x` and nonneg `y`, `Int.fdiv` and `Nat` division agree
under `toNat`. -/
theorem Int.toNat_fdiv_of_nonneg {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x.fdiv y).toNat = x.toNat / y.toNat := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hy
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg b)]
  rfl
