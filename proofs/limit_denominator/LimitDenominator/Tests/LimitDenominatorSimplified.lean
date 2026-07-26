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

/- Both arms of the final comparison are reached. Which arm a case takes is not visible in its
tuple, so this pins representatives: `(7, 5, 3)` returns the extended candidate, `(3, 8, 2)` the
loop candidate. -/
#guard limitDenominatorCases.any fun (m, n, l, _, _) => (m, n, l) == (7, 5, 3)
#guard limitDenominatorCases.any fun (m, n, l, _, _) => (m, n, l) == (3, 8, 2)

/-! ## Exceptions -/

#guard assertRaisesValueError "max_denominator should be at least 1"
  (limitDenominatorSimplified 22 7 0)
#guard assertRaisesValueError "max_denominator should be at least 1"
  (limitDenominatorSimplified 22 7 (-1))

#guard assertRaisesValueError "denominator should be positive"
  (limitDenominatorSimplified 22 0 5)
#guard assertRaisesValueError "denominator should be positive"
  (limitDenominatorSimplified 22 (-7) 5)
#guard assertRaisesValueError "denominator should be positive"
  (limitDenominatorSimplified (-22) (-7) 5)

/- The denominator limit is checked before the target, so its message wins when both are bad. -/
#guard assertRaisesValueError "max_denominator should be at least 1"
  (limitDenominatorSimplified 22 (-7) 0)

/-! ## The specification, evaluated -/

#guard specCheckGrid.all fun (m, n, l) =>
  match limitDenominatorSimplified m n l with
  | .ok (r, s) => checkBestApproximation m n l r s
  | .error _ => false
