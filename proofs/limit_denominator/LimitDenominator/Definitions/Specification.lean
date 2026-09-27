module

public import LimitDenominator.Definitions.Exceptions
public import LimitDenominator.Definitions.IntAbs

/-!
Definition of correctness for a function claiming to compute, among the fractions
whose denominator is at most a given limit, the one closest to a target fraction.
-/

@[expose] public section

/-- Statement that a possibly-exception-raising computation returns a value. -/
def returns {α : Type} (x : PyExcept α) (a : α) := x = .ok a

/-- Statement that a possibly-exception-raising computation raises an exception. -/
def raises {α : Type} (x : PyExcept α) (e : PyException) := x = .error e

/--
The distance from `m / n` to `r / s`, scaled by `n * s`: `|r/s - m/n| * n * s`, for
positive denominators `n` and `s`.
-/
def scaledDistance (m n r s : Int) : Int := (r * n - m * s).abs

/--
`r / s` is at least as good an approximation to `m / n` as `y / z` is: strictly closer,
or equally close with `s ≤ z`. Both sides of each comparison are the distance scaled by
`n * s * z`.
-/
def isBetterApproximation (m n r s y z : Int) : Prop :=
  scaledDistance m n r s * z < scaledDistance m n y z * s
  ∨ scaledDistance m n r s * z = scaledDistance m n y z * s ∧ s ≤ z

/--
What it means for `r / s` to be the best approximation to `m / n` with denominator at
most `l`: closest, with ties broken towards the smaller denominator.

Being in lowest terms is deliberately *not* stipulated here. It follows from the
tie-break alone, because an unreduced pair is equally close as its own reduction, which
has the smaller denominator — see `isBestApproximation.gcd_eq_one`. So once the value is
fixed, so is the representation.
-/
def isBestApproximation (m n l r s : Int) : Prop :=
  0 < s ∧ s ≤ l ∧
  ∀ y z : Int, 0 < z → z ≤ l → isBetterApproximation m n r s y z

/--
The limit is `1` and `m / n` is a half-integer, `w + 1/2` for some integer `w`.

This is the one case in which `isBestApproximation` does not determine the answer, for
a positive target denominator: `⌊m/n⌋ / 1` and `(⌊m/n⌋ + 1) / 1` both satisfy it, being
equidistant from the target at the same denominator.
-/
def isAmbiguous (m n l : Int) : Prop := l = 1 ∧ ∃ w : Int, 2 * m = (2 * w + 1) * n

/--
Statement that a function has the correct behaviour on `valid` targets: raises a
`valueError` with the expected message when the denominator limit is not positive, and
otherwise returns the best approximation.
-/
def isCorrectLimitDenominator
    (valid : Int → Int → Prop)
    (limitDenominator : Int → Int → Int → PyExcept (Int × Int)) :=
  (∀ {m n l : Int}, l ≤ 0 →
      raises (limitDenominator m n l) (.valueError "max_denominator should be at least 1"))
  ∧
  (∀ {m n l : Int}, valid m n → 0 < l →
      ∃ r s, returns (limitDenominator m n l) (r, s) ∧ isBestApproximation m n l r s)

end
