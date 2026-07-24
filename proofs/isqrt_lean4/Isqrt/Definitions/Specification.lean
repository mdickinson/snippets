module

public import Isqrt.Definitions.Exceptions

/-!
Definition of correctness for a function claiming to be an integer square root.
-/

@[expose] public section

/-- Statement that a possibly-exception-raising computation returns a value. -/
def returns {α : Type} (x : PyExcept α) (a : α) := x = .ok a

/-- Statement that a possibly-exception-raising computation raises an exception. -/
def raises {α : Type} (x : PyExcept α) (e : PyException) := x = .error e

/-- What it means for a nonnegative integer `a` to be an integer square root of `n`. -/
def isIntegerSquareRoot (n a : Int) := 0 ≤ a ∧ a * a ≤ n ∧ n < (a + 1) * (a + 1)

/-- What it means for a positive integer `a` to be a *near square root* of `n`. -/
def isNearSquareRoot (n a : Int) := 0 < a ∧ (a - 1) * (a - 1) < n ∧ n < (a + 1) * (a + 1)

/--
Statement that a function `isqrt` has the correct behaviour: raises a `valueError` with
the expected message for all negative inputs, and returns an integer square root for
all nonnegative inputs.
-/
def isCorrectIsqrt (isqrt : Int → PyExcept Int) :=
  (∀ {n : Int}, n < 0 → raises (isqrt n) (.valueError "isqrt() argument must be nonnegative"))
  ∧
  (∀ {n : Int}, 0 ≤ n → ∃ a, returns (isqrt n) a ∧ isIntegerSquareRoot n a)

end
