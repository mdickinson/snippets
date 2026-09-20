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
`r / s` is at least as close to `m / n` as `y / z` is, for a positive denominator `n`
and positive candidate denominators `s` and `z`. Both sides of
`|r/s - m/n| ≤ |y/z - m/n|` are scaled by the positive quantity `n * s * z`.
-/
def atLeastAsClose (m n r s y z : Int) : Prop :=
  (r * n - m * s).abs * z ≤ (y * n - m * z).abs * s

/--
What it means for `r / s` to be the best approximation to `m / n` with denominator at
most `l`: closest, with ties broken towards the smaller denominator.

Being in lowest terms is deliberately *not* stipulated here. It follows from the two
clauses alone, because an unreduced pair is beaten on the second one by its own
reduction — see `isBestApproximation.gcd_eq_one` in
`LimitDenominator.Proofs.BestApproximation`. So once the value is fixed, so is the
representation.
-/
def isBestApproximation (m n l r s : Int) : Prop :=
  0 < s ∧ s ≤ l ∧
  ∀ y z : Int, 0 < z → z ≤ l →
    atLeastAsClose m n r s y z
    ∧ (atLeastAsClose m n y z r s → s ≤ z)

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
