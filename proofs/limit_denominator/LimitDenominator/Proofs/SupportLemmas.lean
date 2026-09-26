module

public import LimitDenominator.Definitions.IntAbs

/-!
General `Int` facts missing from the core library: basic properties of `Int.abs`, and
the Bézout route to lowest terms.
-/

/-! ## Absolute value -/

/-- The absolute value is nonnegative. -/
public theorem Int.abs_nonneg (a : Int) : 0 ≤ a.abs := by unfold Int.abs; split <;> omega

/-- What it takes for an absolute value to equal a given nonnegative integer. -/
public theorem Int.abs_eq (a : Int) {b : Int} : 0 ≤ b → (a.abs = b ↔ a = b ∨ a = -b) := by
  unfold Int.abs; split <;> omega

/-- `Int.abs` is `Int.natAbs`, which is what makes it multiplicative. -/
private theorem Int.abs_eq_natAbs (a : Int) : a.abs = a.natAbs := by unfold Int.abs; split <;> omega

/-- The absolute value is multiplicative. -/
public theorem Int.abs_mul (a b : Int) : (a * b).abs = a.abs * b.abs := by
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.natAbs_mul]; rfl

/-! ## Lowest terms -/

/--
A Bézout identity certifies lowest terms: any common divisor of `r` and `s` divides the
combination, hence divides `1`.
-/
public theorem Int.gcd_eq_one_of_bezout {g h r s : Int} (hb : g * r + h * s = 1) :
    Int.gcd r s = 1 :=
  Int.gcd_eq_one_iff.mpr fun _ cr cs =>
    hb ▸ Int.dvd_add (Int.dvd_mul_of_dvd_right cr) (Int.dvd_mul_of_dvd_right cs)
