/-
The specification — *what "correct" means* for an integer square root. Part of
the **definitions** layer, the trust surface: a reader must read and trust this
module to know the correctness proofs (`Isqrt.Proofs.RecursiveCorrectness`,
`Isqrt.Proofs.IterativeCorrectness`) prove the right thing.

Two definitions, the second built on the first:
* `isIntegerSquareRoot a n` — the postcondition: `a = ⌊√n⌋`.
* `isCorrectIsqrt f` — the top-level contract the two `isqrt` translations
  satisfy, characterising the result by cases (`.ok` ⟹ nonnegative input and an
  exact root; `.error` ⟹ negative input and exactly CPython's `ValueError`).

Single-sourcing the contract here — rather than restating the `match` inside each
theorem — puts the specification itself in the trust surface. `isCorrectIsqrt` is
parameterised by the implementation `f`, so this module depends only on the
`Except`/`PyException` vocabulary (`Isqrt.Definitions.PythonOps`), never on the
`isqrt` definitions themselves. (The proof-only companion predicate
`isNearSquareRoot` lives with the key algebraic lemma in `Isqrt.Proofs.KeyLemma`.)
-/

import Isqrt.Definitions.PythonOps

/-- `a` is *the* integer square root of `n` if `a² ≤ n < (a + 1)²`, i.e.
`a = ⌊√n⌋` exactly. This is the postcondition the top-level correctness theorems
assert. Stated multiplicatively (`a * a`, not `a ^ 2`) to mirror the Python
postcondition `a * a <= n < (a + 1) * (a + 1)`. -/
def isIntegerSquareRoot (a n : Int) : Prop := a * a ≤ n ∧ n < (a + 1) * (a + 1)

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
