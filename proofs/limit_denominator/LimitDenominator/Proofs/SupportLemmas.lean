module

public import LimitDenominator.Definitions.IntAbs

/-!
General `Int` facts missing from the core library: basic properties of `Int.abs`, and
the two divisibility facts the fast path needs, lowest terms being what makes its
rival's denominator a multiple of the target's.
-/

/-! ## Absolute value -/

/-- The absolute value is nonnegative. -/
public theorem Int.abs_nonneg (a : Int) : 0 ≤ a.abs := by unfold Int.abs; split <;> omega

/-- What it takes for an absolute value to equal a given nonnegative integer. -/
public theorem Int.abs_eq (a : Int) {b : Int} : 0 ≤ b → (a.abs = b ↔ a = b ∨ a = -b) := by
  unfold Int.abs; split <;> omega

/-- Only zero has zero absolute value. -/
public theorem Int.abs_eq_zero {a : Int} : a.abs = 0 ↔ a = 0 := by
  unfold Int.abs; split <;> omega

/-- `Int.abs` is `Int.natAbs`, which is what makes it multiplicative. -/
private theorem Int.abs_eq_natAbs (a : Int) : a.abs = a.natAbs := by unfold Int.abs; split <;> omega

/-- The absolute value is multiplicative. -/
public theorem Int.abs_mul (a b : Int) : (a * b).abs = a.abs * b.abs := by
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.natAbs_mul]; rfl

/-! ## Lowest terms and divisibility -/

/--
A Bézout identity certifies lowest terms: any common divisor of `r` and `s` divides the
combination, hence divides `1`.
-/
public theorem Int.gcd_eq_one_of_bezout {g h r s : Int} (hb : g * r + h * s = 1) :
    Int.gcd r s = 1 :=
  Int.gcd_eq_one_iff.mpr fun _ cr cs =>
    hb ▸ Int.dvd_add (Int.dvd_mul_of_dvd_right cr) (Int.dvd_mul_of_dvd_right cs)

/--
If `y / z` equals `r / s` as a value and `r / s` is in lowest terms, then `s` divides `z`.
-/
private theorem Int.dvd_of_mul_eq_mul_of_gcd_eq_one {r s y z : Int}
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
