/-
The specification — *what "correct" means* for an integer square root. Part of
the **definitions** layer, the trust surface: a reader must read and trust this
module to know the correctness proofs (`Isqrt.Proofs.RecursiveCorrectness`,
`Isqrt.Proofs.IterativeCorrectness`) prove the right thing.

The contract `isCorrectIsqrt` is stated with the four small `PyExcept` helpers from
`Isqrt.Definitions.Exceptions` — `succeeds`/`fails` (it returned / it raised) and
the proof-carrying extractors `returnValue`/`exceptionRaised` (the returned value /
the raised exception, total only given a proof that the computation took that
branch). Each clause then reads as the property we actually want, applied to the
real returned value or raised exception, with the sign of the argument as a
hypothesis: for nonnegative `n` the function returns the integer square root; for
negative `n` it raises CPython's `ValueError`.

`isCorrectIsqrt` is parameterised by the implementation `f`, so this module
depends only on the `PyExcept`/`PyException` vocabulary (`Isqrt.Definitions.Exceptions`),
never on the `isqrt` definitions themselves. (The proof-only companion predicate
`isNearSquareRoot` lives with the key algebraic lemma in `Isqrt.Proofs.KeyLemma`.)
-/

import Isqrt.Definitions.Exceptions

/-- `a` is *the* integer square root of `n` if `a² ≤ n < (a + 1)²`, i.e.
`a = ⌊√n⌋` exactly. This is the postcondition asserted of a returned value.
Stated multiplicatively (`a * a`, not `a ^ 2`) to mirror the Python postcondition
`a * a <= n < (a + 1) * (a + 1)`. -/
def isIntegerSquareRoot (a n : Int) : Prop := a * a ≤ n ∧ n < (a + 1) * (a + 1)

/-- `isqrt` is a correct integer square root:
* for every nonnegative `n`, `isqrt n` succeeds (does not raise) and the value it
  returns is the integer square root of `n` (`isIntegerSquareRoot`);
* for every negative `n`, `isqrt n` raises exactly the `ValueError` CPython's
  `math.isqrt` raises, message and all.

Stated with the proof-carrying `succeeds`/`returnValue` and `fails`/`exceptionRaised`
helpers, so each clause reads as the property we want of the actual returned value
or raised exception. The error message is part of the contract. -/
def isCorrectIsqrt (isqrt : Int → PyExcept Int) : Prop :=
  (∀ n, 0 ≤ n → ∃ h : Isqrt.succeeds (isqrt n), isIntegerSquareRoot (Isqrt.returnValue (isqrt n) h) n)
  ∧
  (∀ n, n < 0 → ∃ h : Isqrt.fails (isqrt n), Isqrt.exceptionRaised (isqrt n) h = .valueError "isqrt() argument must be nonnegative")
