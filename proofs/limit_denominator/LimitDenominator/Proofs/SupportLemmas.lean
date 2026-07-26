module

public import LimitDenominator.Definitions.Specification

/-!
General `Int` facts missing from the core library: monotonicity of multiplication in the
shape the bracket argument needs, basic properties of the specification's `Int.abs`, and the
two divisibility facts that unit determinants buy us.
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

/-! ## Consequences of a unit determinant -/

/--
A unit determinant against any other pair implies coprimality: if `t * s - r * u` is `±1`
then `r` and `s` are coprime, since any common divisor of `r` and `s` divides that unit.
-/
public theorem Int.gcd_eq_one_of_det {r s t u : Int}
    (h : t * s - r * u = 1 ∨ t * s - r * u = -1) : Int.gcd r s = 1 := by
  obtain ⟨c, hc⟩ := Int.gcd_dvd_right r s
  obtain ⟨e, he⟩ := Int.gcd_dvd_left r s
  have hdvd : ((Int.gcd r s : Nat) : Int) ∣ t * s - r * u := ⟨t * c - e * u, by grind⟩
  have hone : ((Int.gcd r s : Nat) : Int) = 1 := by
    rcases h with h | h <;> rw [h] at hdvd
    · exact Int.eq_one_of_dvd_one (by omega) hdvd
    · exact Int.eq_one_of_dvd_one (by omega) (Int.dvd_neg.mp hdvd)
  omega

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
