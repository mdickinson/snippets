module

public import LimitDenominator.Definitions.Exceptions

/-!
Definition of correctness for a function claiming to compute the closest fraction to a
target with a bounded denominator.
-/

@[expose] public section

/-- Statement that a possibly-exception-raising computation returns a value. -/
def returns {α : Type} (x : PyExcept α) (a : α) := x = .ok a

/-- Statement that a possibly-exception-raising computation raises an exception. -/
def raises {α : Type} (x : PyExcept α) (e : PyException) := x = .error e

/-- Absolute value of an integer. -/
def Int.abs (a : Int) : Int := if 0 ≤ a then a else -a

/--
`(r, s)` is at least as close to `m / n` as `(y, z)` is, for positive denominators `s` and
`z`. Both sides of `|m/n - r/s| ≤ |m/n - y/z|` are scaled by the positive quantity
`n * s * z`.
-/
def atLeastAsClose (m n r s y z : Int) : Prop :=
  (m * s - r * n).abs * z ≤ (m * z - y * n).abs * s

/--
What it means for `r / s` to be the best approximation to `m / n` with denominator at most
`l`: closest, with ties broken towards the smaller denominator and any remaining tie
towards the smaller fraction, in lowest terms.
-/
def isBestApproximation (m n l r s : Int) : Prop :=
  0 < s ∧ s ≤ l ∧ Int.gcd r s = 1 ∧
  ∀ y z : Int, 0 < z → z ≤ l →
    atLeastAsClose m n r s y z
    ∧ (atLeastAsClose m n y z r s → s ≤ z)
    ∧ (atLeastAsClose m n y z r s → s = z → r ≤ y)

/--
Statement that a function has the correct behaviour on `valid` targets: raises a
`valueError` with the expected message when the denominator limit is less than one, and
otherwise returns the best approximation.
-/
def isCorrectLimitDenominator
    (valid : Int → Int → Prop)
    (limitDenominator : Int → Int → Int → PyExcept (Int × Int)) :=
  (∀ {m n l : Int}, l < 1 →
      raises (limitDenominator m n l) (.valueError "max_denominator should be at least 1"))
  ∧
  (∀ {m n l : Int}, valid m n → 1 ≤ l →
      ∃ r s, returns (limitDenominator m n l) (r, s) ∧ isBestApproximation m n l r s)

end
