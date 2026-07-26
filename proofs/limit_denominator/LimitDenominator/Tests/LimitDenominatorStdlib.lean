module

meta import LimitDenominator.Definitions.LimitDenominatorSimplified
meta import LimitDenominator.Definitions.LimitDenominatorStdlib
meta import LimitDenominator.Tests.Assertions
meta import LimitDenominator.Tests.SpecCheck
meta import LimitDenominator.Tests.Vectors

/-!
Tests for `limitDenominatorStdlib`: the expected-value vectors, the exception case, the
executable form of the specification over a grid of targets, and agreement with the simplified
listing over that same grid.

This listing's target must be in lowest terms with a positive denominator, which the grid's
targets are not all in, so the two grid checks skip the rest rather than expecting anything of
them.
-/

/-! ## Expected values -/

#guard limitDenominatorStdlibCases.all fun (m, n, l, r, s) =>
  assertReturns (limitDenominatorStdlib m n l) (r, s)

/- Both paths are reached by the vectors: the fast path when `n ≤ l`, the loop otherwise. -/
#guard limitDenominatorStdlibCases.any fun (_, n, l, _, _) => n ≤ l
#guard limitDenominatorStdlibCases.any fun (_, n, l, _, _) => l < n

/-! ## Exceptions -/

/- A nonpositive limit is the only exception this listing can raise: its target's denominator is
a precondition rather than a test, and the fast path is what makes both divisions safe. -/
#guard assertRaisesValueError "max_denominator should be at least 1"
  (limitDenominatorStdlib 22 7 0)
#guard assertRaisesValueError "max_denominator should be at least 1"
  (limitDenominatorStdlib 22 7 (-1))

/-! ## The specification, evaluated -/

/- Being gated on `Int.gcd m n = 1`, both grid checks below could have passed vacuously. Neither
does: a clear majority of the grid's targets are in lowest terms, and among those both tie-break
clauses have live antecedents for either sign of `m` — clause 3's only at a limit of one, which
§ "The degenerate tie" of PROOF.md shows is the only place they can be. To re-derive, filter
`specCheckGrid` to targets in lowest terms and count those with a rival that ties on distance at
a different denominator (clause 2) or at the same one (clause 3). -/

#guard specCheckGrid.all fun (m, n, l) =>
  Int.gcd m n != 1 ||
    match limitDenominatorStdlib m n l with
    | .ok (r, s) => checkBestApproximation m n l r s
    | .error _ => false

/-! ## Agreement with the simplified listing -/

#guard specCheckGrid.all fun (m, n, l) =>
  Int.gcd m n != 1 ||
    match limitDenominatorSimplified m n l with
    | .ok (r, s) => assertReturns (limitDenominatorStdlib m n l) (r, s)
    | .error _ => false
