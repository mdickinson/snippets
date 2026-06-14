/-
The top-level correctness specification for an integer-square-root implementation.
Part of the **definitions** layer: `isCorrectIsqrt f` is the contract the
correctness proofs (`Isqrt.Proofs.RecursiveCorrectness`,
`Isqrt.Proofs.IterativeCorrectness`) establish of the two `isqrt` translations, so
a reader must read and trust it to know *what* those proofs prove.

Single-sourcing the contract here — rather than restating the `match` inside each
theorem — puts the specification itself in the trust surface, not merely the
postcondition predicate `isIntegerSquareRoot` it builds on. The spec is
parameterised by the implementation `f`, so it depends only on the predicate and
the `Except`/`PyException` vocabulary, never on the `isqrt` definitions themselves.
-/

import Isqrt.Definitions.PythonOps
import Isqrt.Definitions.IntegerSquareRoot

/-- `f` is a correct integer square root: for every argument `n` it either returns
`.ok v` with `v = ⌊√n⌋` (`isIntegerSquareRoot v n`) for a nonnegative `n`, or
raises exactly the `ValueError` CPython's `math.isqrt` raises on a negative
argument. This is the total specification the correctness proofs establish of both
`isqrtRecursive` (`Isqrt.Definitions.Recursive`) and `isqrtIterative`
(`Isqrt.Definitions.Iterative`).

The error message is part of the contract: the spec pins the exact CPython text,
matching the `throw` in each translation. -/
def isCorrectIsqrt (f : Int → Except PyException Int) : Prop :=
  ∀ n, match f n with
       | .ok v => 0 ≤ n ∧ isIntegerSquareRoot v n
       | .error e => n < 0 ∧ e = .valueError "isqrt() argument must be nonnegative"
