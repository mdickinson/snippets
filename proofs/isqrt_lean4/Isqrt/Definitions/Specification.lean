/-
The specification — *what "correct" means* for an integer square root. Part of
the **definitions** layer, the trust surface: a reader must read and trust this
module to know the correctness proofs (`Isqrt.Proofs.RecursiveCorrectness`,
`Isqrt.Proofs.IterativeCorrectness`) prove the right thing.

The contract `isCorrectIsqrt` is stated with four small helpers on an `Except`
result — `succeeded`/`failed` (it returned / it raised) and the proof-carrying
extractors `returnValue`/`exception` (the returned value / the raised exception,
total only given a proof that the computation took that branch). Each clause then
reads as the property we actually want, applied to the real returned value or
raised exception, with the sign of the argument as a hypothesis: for nonnegative
`n` the function returns the integer square root; for negative `n` it raises
CPython's `ValueError`.

`isCorrectIsqrt` is parameterised by the implementation `f`, so this module
depends only on the `Except`/`PyException` vocabulary (`Isqrt.Definitions.PythonOps`),
never on the `isqrt` definitions themselves. (The proof-only companion predicate
`isNearSquareRoot` lives with the key algebraic lemma in `Isqrt.Proofs.KeyLemma`.)
-/

import Isqrt.Definitions.PythonOps

/-- `a` is *the* integer square root of `n` if `a² ≤ n < (a + 1)²`, i.e.
`a = ⌊√n⌋` exactly. This is the postcondition asserted of a returned value.
Stated multiplicatively (`a * a`, not `a ^ 2`) to mirror the Python postcondition
`a * a <= n < (a + 1) * (a + 1)`. -/
def isIntegerSquareRoot (a n : Int) : Prop := a * a ≤ n ∧ n < (a + 1) * (a + 1)

/-- Assertion that a computation didn't raise. -/
def succeeded {ε α : Type _} (x : Except ε α) : Prop := match x with
  | .ok _ => True
  | .error _ => False

/-- The return value from a computation that didn't raise. -/
def returnValue {ε α : Type _} (x : Except ε α) (p : succeeded x) : α :=
  match x with
  | .ok a => a

/-- Assertion that a computation failed. -/
def failed {ε α : Type _} (x : Except ε α) : Prop := match x with
  | .ok _ => False
  | .error _ => True

/-- The exception raised by a failed computation. -/
def exception {ε α : Type _} (x : Except ε α) (p : failed x) : ε :=
  match x with
  | .error e => e

/-- `f` is a correct integer square root:
* for every nonnegative `n`, `f n` succeeds (does not raise) and the value it
  returns is the integer square root of `n` (`isIntegerSquareRoot`);
* for every negative `n`, `f n` raises exactly the `ValueError` CPython's
  `math.isqrt` raises, message and all.

Stated with the proof-carrying `succeeded`/`returnValue` and `failed`/`exception`
helpers, so each clause reads as the property we want of the actual returned value
or raised exception. The error message is part of the contract. -/
def isCorrectIsqrt (f : Int → Except PyException Int) : Prop :=
  (∀ n, 0 ≤ n → let v := f n; ∃ h : succeeded v, isIntegerSquareRoot (returnValue v h) n)
  ∧
  (∀ n, n < 0 → let v := f n; ∃ h : failed v, exception v h = .valueError "isqrt() argument must be nonnegative")
