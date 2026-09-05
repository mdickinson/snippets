module

public import LimitDenominator.Definitions.PythonPrimitives

/-!
Assertion helpers for the `#guard`-based sanity checks in `LimitDenominator.Tests.*`.

The Python primitives and the translation return `PyExcept`, which a bare `#guard` cannot
compare (`PyException` has no `DecidableEq`). These helpers unwrap a result into a `Bool` that
`#guard` can check.
-/

@[expose] public section

/-- True when the computation returned `.ok expected`. -/
def assertReturns {α : Type} [BEq α] (actual : PyExcept α) (expected : α) : Bool :=
  match actual with
  | .ok v => v == expected
  | .error _ => false

/-- True when the computation raised `ZeroDivisionError`. -/
def assertRaisesZeroDivisionError {α : Type} (actual : PyExcept α) : Bool :=
  match actual with
  | .error (.zeroDivisionError _) => true
  | _ => false

/-- True when the computation raised `ValueError msg`. -/
def assertRaisesValueError {α : Type} (msg : String) (actual : PyExcept α) : Bool :=
  match actual with
  | .error (.valueError m) => m == msg
  | _ => false

end
