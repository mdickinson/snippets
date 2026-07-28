module

public import LimitDenominator.Definitions.Specification

/-!
General `Int` facts missing from the core library: monotonicity of multiplication in the
shape the bracket argument needs, basic properties of the specification's `Int.abs`, and the
two divisibility facts the fast path needs, lowest terms being what makes its rival's
denominator a multiple of the target's.
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

/-- Multiplying by `1` or `-1` never exceeds the absolute value. -/
public theorem Int.mul_sign_le_abs {a d : Int} (hd : d = 1 ∨ d = -1) : a * d ≤ a.abs := by
  unfold Int.abs; rcases hd with rfl | rfl <;> split <;> omega

/-- Negating too: `-(a * d)` never exceeds the absolute value either. -/
public theorem Int.neg_mul_sign_le_abs {a d : Int} (hd : d = 1 ∨ d = -1) : -(a * d) ≤ a.abs := by
  unfold Int.abs; rcases hd with rfl | rfl <;> split <;> omega

/--
The scaled form of `Int.mul_sign_le_abs`. Both this and `Int.neg_mul_sign_mul_le_abs_mul` are
stated with the scaling already applied, so that `omega` sees the same product atoms as the
pivot identities do.
-/
public theorem Int.mul_sign_mul_le_abs_mul {a d e : Int} (hd : d = 1 ∨ d = -1) (he : 0 ≤ e) :
    a * d * e ≤ a.abs * e :=
  Int.mul_le_mul_of_nonneg_right (Int.mul_sign_le_abs hd) he

/-- The scaled form of `Int.neg_mul_sign_le_abs`. -/
public theorem Int.neg_mul_sign_mul_le_abs_mul {a d e : Int} (hd : d = 1 ∨ d = -1) (he : 0 ≤ e) :
    -(a * d * e) ≤ a.abs * e := by
  have h := Int.mul_le_mul_of_nonneg_right (Int.neg_mul_sign_le_abs (a := a) hd) he
  rwa [Int.neg_mul] at h

/-- If `a * d = b` with `d` a sign and `b` nonnegative, then `b` is the absolute value of `a`. -/
public theorem Int.abs_eq_of_mul_sign {a b d : Int}
    (hd : d = 1 ∨ d = -1) (hb : 0 ≤ b) (h : a * d = b) : a.abs = b := by
  unfold Int.abs; rcases hd with rfl | rfl <;> split <;> omega

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
