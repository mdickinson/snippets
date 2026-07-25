module

meta import LimitDenominator.Definitions.LimitDenominatorSimplified
meta import LimitDenominator.Tests.Assertions
meta import LimitDenominator.Tests.SpecCheck
meta import LimitDenominator.Tests.Vectors

/-!
Tests for `limitDenominatorSimplified`: the expected-value vectors, the exception cases, and the
executable form of the specification over a grid of targets.
-/

/-! ## Expected values -/

#guard limitDenominatorCases.all fun (m, n, l, r, s) =>
  assertReturns (limitDenominatorSimplified m n l) (r, s)

/-! ## Exceptions -/

#guard assertRaisesValueError "max_denominator should be at least 1"
  (limitDenominatorSimplified 22 7 0)
#guard assertRaisesValueError "max_denominator should be at least 1"
  (limitDenominatorSimplified 22 7 (-1))

/-
A zero target denominator is outside the specification — `Fraction` cannot produce one — and the
`%` in the very first line is what reports it.
-/
#guard assertRaisesZeroDivisionError (limitDenominatorSimplified 22 0 5)

/-! ## The specification, evaluated -/

#guard specCheckGrid.all fun (m, n, l) =>
  match limitDenominatorSimplified m n l with
  | .ok (r, s) => checkBestApproximation m n l r s
  | .error _ => false
