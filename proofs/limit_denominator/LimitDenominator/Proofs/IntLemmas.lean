module

public import LimitDenominator.Definitions.IntAbs

/-!
General `Int` facts missing from the core library: basic properties of `Int.abs`, the
signs of products, multiplying and cancelling a positive factor, and the Bézout route to
lowest terms.
-/

/-! ## Absolute value -/

/-- The absolute value is nonnegative. -/
public theorem Int.abs_nonneg (a : Int) : 0 ≤ a.abs := by
  unfold Int.abs; split <;> omega

/-- What it takes for an absolute value to equal a given nonnegative integer. -/
public theorem Int.abs_eq (a : Int) {b : Int} :
    0 ≤ b → (a.abs = b ↔ a = b ∨ a = -b) := by
  unfold Int.abs; split <;> omega

/-- `Int.abs` is `Int.natAbs`, which is what makes it multiplicative. -/
private theorem Int.abs_eq_natAbs (a : Int) : a.abs = a.natAbs := by
  unfold Int.abs; split <;> omega

/-- The absolute value is multiplicative. -/
public theorem Int.abs_mul (a b : Int) : (a * b).abs = a.abs * b.abs := by
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.natAbs_mul]; rfl

/-! ## Units and signs -/

/-- The only factors of 1 are 1 and -1. -/
public theorem Int.eq_one_or_neg_one_of_mul_eq_one {a b : Int} (hab : a * b = 1) :
    a = 1 ∨ a = -1 := by
  rw [← Int.abs_eq a (by decide)]
  exact Int.eq_one_of_mul_eq_one_right (Int.abs_nonneg a)
    (show a.abs * b.abs = 1 by grind only [Int.abs_mul a b, Int.abs])

/--
A product of two integers is positive iff both are positive or both are negative.
-/
public theorem Int.mul_pos_iff {a b : Int} :
    0 < a * b ↔ (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by
  grind only [Int.lt_trichotomy 0, Int.mul_pos, Int.mul_pos_of_neg_of_neg,
    Int.mul_neg_of_pos_of_neg, Int.mul_neg_of_neg_of_pos]

/--
A product of two integers is nonnegative iff both are nonnegative or both are
nonpositive.
-/
private theorem Int.mul_nonneg_iff {a b : Int} :
    0 ≤ a * b ↔ (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0) := by
  grind only [Int.le_total 0, Int.mul_nonneg, Int.mul_nonneg_of_nonpos_of_nonpos,
    Int.mul_nonpos_of_nonneg_of_nonpos, Int.mul_nonpos_of_nonpos_of_nonneg,
    Int.mul_eq_zero]

/-- Any divisor of a positive product is less than or equal to the product. -/
public theorem Int.divisor_le_mul {a b : Int} (h : 0 < a * b) : a ≤ a * b := by
  grind only [Int.mul_nonneg_iff (a := a) (b := b - 1), Int.mul_pos_iff.mp h]

/--
If a linear combination of two positive integers is positive, then at least one of the
coefficients is positive.
-/
public theorem Int.pos_or_pos_of_lincomb_pos {a b c d : Int}
    (c_pos : 0 < c) (d_pos : 0 < d) (lc_pos : 0 < a * c + b * d) : 0 < a ∨ 0 < b := by
  rcases (show 0 < a * c ∨ 0 < b * d by omega) with h1 | h2
  · left; exact Int.pos_of_mul_pos_left h1 c_pos
  · right; exact Int.pos_of_mul_pos_left h2 d_pos

/-! ## Multiplying and cancelling a positive factor -/

/-
We often need to multiply both sides of an equality or inequality by a positive factor,
or to cancel that factor again. These helper lemmas make those operations easy to spell.
-/

/-- Multiply an equality by a positive factor; `_hc` is taken only for uniformity. -/
public theorem Int.eq_mul_pos {a b c : Int} (_hc : 0 < c) (heq : a = b) :
    a * c = b * c := by
  rw [heq]

/-- Multiply a strict inequality by a positive factor. -/
public theorem Int.lt_mul_pos {a b c : Int} (hc : 0 < c) (hlt : a < b) :
    a * c < b * c :=
  Int.mul_lt_mul_of_pos_right hlt hc

/-- Multiply an inequality by a positive factor. -/
public theorem Int.le_mul_pos {a b c : Int} (hc : 0 < c) (hle : a ≤ b) :
    a * c ≤ b * c :=
  Int.mul_le_mul_of_nonneg_right hle (Int.le_of_lt hc)

/-- Cancel a positive factor from an equality. -/
public theorem Int.eq_of_eq_mul_pos {a b c : Int} (hc : 0 < c) (heq : a * c = b * c) :
    a = b :=
  Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hc) heq

/-- Cancel a positive factor from a strict inequality. -/
public theorem Int.lt_of_lt_mul_pos {a b c : Int} (hc : 0 < c) (hlt : a * c < b * c) :
    a < b :=
  Int.lt_of_mul_lt_mul_right hlt (Int.le_of_lt hc)

/-- Cancel a positive factor from an inequality. -/
public theorem Int.le_of_le_mul_pos {a b c : Int} (hc : 0 < c) (hle : a * c ≤ b * c) :
    a ≤ b :=
  Int.le_of_mul_le_mul_right hle hc

/-! ## Lowest terms -/

/--
A Bézout identity certifies lowest terms: any common divisor of `r` and `s` divides the
combination, hence divides `1`.
-/
public theorem Int.gcd_eq_one_of_bezout {g h r s : Int} (hb : g * r + h * s = 1) :
    Int.gcd r s = 1 :=
  Int.gcd_eq_one_iff.mpr fun _ cr cs =>
    hb ▸ Int.dvd_add (Int.dvd_mul_of_dvd_right cr) (Int.dvd_mul_of_dvd_right cs)
