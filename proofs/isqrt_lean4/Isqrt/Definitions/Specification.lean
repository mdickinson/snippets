/-
The specification — *what "correct" means* for an integer square root: the outcome
predicates `returns`/`raises` on a `PyExcept` result, the postcondition predicate
`isIntegerSquareRoot`, and the top-level contract `isCorrectIsqrt`. Core-only: no Mathlib.
-/

import Isqrt.Definitions.Exceptions

/-- `returns x a` asserts that the computation `x` returned the value `a` —
i.e. took its `.ok` branch with payload `a`. -/
def returns {α : Type} (x : PyExcept α) (a : α) : Prop := x = .ok a

/-- `raises x e` asserts that the computation `x` raised the exception `e` —
i.e. took its `.error` branch with payload `e`. -/
def raises {α : Type} (x : PyExcept α) (e : PyException) : Prop := x = .error e

/-- `a` is *the* integer square root of `n` if `a² ≤ n < (a + 1)²`, i.e.
`a = ⌊√n⌋` exactly. Stated multiplicatively (`a * a`, not `a ^ 2`) to mirror the
Python postcondition `a * a <= n < (a + 1) * (a + 1)`. -/
def isIntegerSquareRoot (n a : Int) : Prop := a * a ≤ n ∧ n < (a + 1) * (a + 1)

/-- `isqrt` is a correct integer square root:
* for every nonnegative `n`, `isqrt n` returns a value that is the integer square
  root of `n` (`isIntegerSquareRoot`);
* for every negative `n`, `isqrt n` raises exactly the `ValueError` CPython raises,
  message and all (the message is part of the contract). -/
def isCorrectIsqrt (isqrt : Int → PyExcept Int) : Prop :=
  (∀ n, 0 ≤ n → ∃ a, returns (isqrt n) a ∧ isIntegerSquareRoot n a)
  ∧
  (∀ n, n < 0 → raises (isqrt n) (.valueError "isqrt() argument must be nonnegative"))
