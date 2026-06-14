/-
The specification — *what "correct" means* for an integer square root. Part of
the **definitions** layer, the trust surface: a reader must read and trust this
module to know the correctness proofs (`Isqrt.Proofs.RecursiveCorrectness`,
`Isqrt.Proofs.IterativeCorrectness`) prove the right thing.

The contract `isCorrectIsqrt` is stated directly in terms of *returning* and
*raising* — the `.ok`/`.error` outcomes of an `Except` computation — so it reads
as the two properties we actually want, each guarded by the sign of the argument:
for nonnegative `n` the function returns the integer square root; for negative `n`
it raises CPython's `ValueError`. (`Except.returns` / `Except.raises` are the
`Prop`-level analogues of the `Bool`-valued `assert*` helpers in
`Isqrt.Tests.Assertions`.)

`isCorrectIsqrt` is parameterised by the implementation `f`, so this module
depends only on the `Except`/`PyException` vocabulary (`Isqrt.Definitions.PythonOps`),
never on the `isqrt` definitions themselves. (The proof-only companion predicate
`isNearSquareRoot` lives with the key algebraic lemma in `Isqrt.Proofs.KeyLemma`.)
-/

import Isqrt.Definitions.PythonOps

/-- The computation `x` *returns a value satisfying* `p`: it evaluated to `.ok a`
for some `a` with `p a`, rather than raising. -/
def Except.returns {ε α : Type _} (x : Except ε α) (p : α → Prop) : Prop :=
  ∃ a, x = .ok a ∧ p a

/-- The computation `x` *raises* `e`: it evaluated to `.error e` rather than
returning. -/
def Except.raises {ε α : Type _} (x : Except ε α) (e : ε) : Prop := x = .error e

/-- `a` is *the* integer square root of `n` if `a² ≤ n < (a + 1)²`, i.e.
`a = ⌊√n⌋` exactly. This is the postcondition asserted of a returned value.
Stated multiplicatively (`a * a`, not `a ^ 2`) to mirror the Python postcondition
`a * a <= n < (a + 1) * (a + 1)`. -/
def isIntegerSquareRoot (a n : Int) : Prop := a * a ≤ n ∧ n < (a + 1) * (a + 1)

/-- `f` is a correct integer square root:
* for every nonnegative `n`, `f n` returns a value `a` that is the integer square
  root of `n` (`isIntegerSquareRoot a n`);
* for every negative `n`, `f n` raises exactly the `ValueError` CPython's
  `math.isqrt` raises, message and all.

The error message is part of the contract, matching the `throw` in each
translation. -/
def isCorrectIsqrt (f : Int → Except PyException Int) : Prop :=
  (∀ n, 0 ≤ n → (f n).returns (fun a => isIntegerSquareRoot a n)) ∧
  (∀ n, n < 0 → (f n).raises (.valueError "isqrt() argument must be nonnegative"))
