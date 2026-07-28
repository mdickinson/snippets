module

public import LimitDenominator.Definitions.Specification

/-!
General `Int` facts missing from the core library: monotonicity of multiplication in the
shape the bracket argument needs, basic properties of the specification's `Int.abs`, the
cancellation that removes the orientation from an inequality, and the two divisibility facts
the fast path needs, lowest terms being what makes its rival's denominator a multiple of the
target's.
-/

/-! ## Multiplication and order -/

/-- Multiplying a nonnegative integer by something at least one can only increase it. -/
public theorem Int.le_mul_of_one_le_left {a b : Int} (hb : 0 ≤ b) (ha : 1 ≤ a) : b ≤ a * b := by
  have := Int.mul_le_mul_of_nonneg_right ha hb
  omega

/-! ## Absolute value -/

/-- The absolute value is nonnegative. -/
public theorem Int.abs_nonneg (a : Int) : 0 ≤ a.abs := by unfold Int.abs; split <;> omega

/-- Only zero has zero absolute value. -/
public theorem Int.abs_eq_zero {a : Int} : a.abs = 0 ↔ a = 0 := by
  unfold Int.abs; split <;> omega

/-- A positive factor comes out of the absolute value. -/
public theorem Int.abs_mul_of_pos {a b : Int} (ha : 0 < a) : (a * b).abs = a * b.abs := by
  unfold Int.abs
  rcases (by omega : 0 ≤ b ∨ b < 0) with hb | hb
  · rw [if_pos (Int.mul_nonneg (by omega) hb), if_pos hb]
  · rw [if_neg (by have := Int.mul_neg_of_pos_of_neg ha hb; omega), if_neg (by omega)]
    grind

/-- Negating leaves the absolute value alone. -/
public theorem Int.abs_neg (a : Int) : (-a).abs = a.abs := by unfold Int.abs; split <;> omega

/-- `Int.abs` is `Int.natAbs`, which is what makes it multiplicative. -/
private theorem Int.abs_eq_natAbs (a : Int) : a.abs = a.natAbs := by unfold Int.abs; split <;> omega

/-- The absolute value is multiplicative. -/
private theorem Int.abs_mul (a b : Int) : (a * b).abs = a.abs * b.abs := by
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.natAbs_mul]; rfl

/-! ## Cancelling the orientation -/

/--
Rewriting the two ends of an oriented chain so that a factor of `|v|` stands on each side. The
lower end is an equality because it is nonnegative, the upper end only an inequality.
-/
private theorem Int.abs_chain {x y v z w : Int} (hz : 0 < z) (hw : 0 < w)
    (hnonneg : 0 ≤ x * v * z) :
    x.abs * z * v.abs = x * v * z ∧ y * v * w ≤ y.abs * w * v.abs := by
  refine ⟨?_, ?_⟩
  · rw [← show (x * v * z).abs = x * v * z from by unfold Int.abs; omega,
      Int.abs_mul, Int.abs_mul, show z.abs = z from by unfold Int.abs; omega]
    grind
  · have h1 : y * v * w ≤ (y * v * w).abs := by unfold Int.abs; omega
    rw [Int.abs_mul, Int.abs_mul, show w.abs = w from by unfold Int.abs; omega] at h1
    grind

/--
Cancelling the orientation, with the equality case every caller wants alongside it. An inequality
between two oriented scaled distances, the lower end nonnegative, becomes the same inequality on
absolute values with the orientation gone; and a candidate matching the bound afterwards matched
it before, the chain being squeezed between equal ends.

Taking absolute values puts a factor of `|v|` on both sides, and a nonzero `|v|` is positive, so
it cancels. That needs only `v ≠ 0` — never that `v` is a unit.
-/
public theorem Int.abs_cancel {x y v z w : Int} (hv : v ≠ 0) (hz : 0 < z) (hw : 0 < w)
    (hnonneg : 0 ≤ x * v * z) (hle : x * v * z ≤ y * v * w) :
    x.abs * z ≤ y.abs * w ∧ (y.abs * w ≤ x.abs * z → x * v * z = y * v * w) := by
  obtain ⟨hx, hy⟩ := Int.abs_chain (y := y) (w := w) hz hw hnonneg
  refine ⟨Int.le_of_mul_le_mul_right (by omega) (show 0 < v.abs by unfold Int.abs; omega), ?_⟩
  intro hrev
  have := Int.mul_le_mul_of_nonneg_right hrev (Int.abs_nonneg v)
  omega

/-- The strict form, which is just the equality case read as a trichotomy. -/
public theorem Int.abs_lt_abs_of_mul_lt_mul {x y v z w : Int} (hv : v ≠ 0) (hz : 0 < z)
    (hw : 0 < w) (hnonneg : 0 ≤ x * v * z) (hlt : x * v * z < y * v * w) :
    x.abs * z < y.abs * w := by
  obtain ⟨hle, heq⟩ := Int.abs_cancel (y := y) hv hz hw hnonneg (by omega)
  rcases (by omega : x.abs * z < y.abs * w ∨ y.abs * w ≤ x.abs * z) with hlt' | hrev
  · exact hlt'
  · have := heq hrev; omega

/-! ## Lowest terms and divisibility -/

/--
If `y / z` equals `r / s` as a value and `r / s` is in lowest terms, then `s` divides `z`.
-/
public theorem Int.dvd_of_mul_eq_mul_of_gcd_eq_one {r s y z : Int}
    (hg : Int.gcd r s = 1) (h : y * s = r * z) : s ∣ z := by
  have hdvd : s ∣ r * z := ⟨y, by rw [← h]; exact Int.mul_comm y s⟩
  have hnat : s.natAbs ∣ r.natAbs * z.natAbs := by
    rw [← Int.natAbs_mul]; exact Int.natAbs_dvd_natAbs.mpr hdvd
  exact Int.natAbs_dvd_natAbs.mp (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hg) hnat)

/--
The denominator of a fraction in lowest terms is at most that of any equal fraction with a
positive denominator.
-/
public theorem Int.le_of_mul_eq_mul_of_gcd_eq_one {r s y z : Int}
    (hg : Int.gcd r s = 1) (hz : 0 < z) (h : y * s = r * z) : s ≤ z :=
  Int.le_of_dvd hz (Int.dvd_of_mul_eq_mul_of_gcd_eq_one hg h)
