/-
Assertion helpers for the `#guard`-based sanity checks in `Isqrt.Tests.*`.

The operations behind `math.isqrt` return `Except PyException Int`, which a bare
`#guard` cannot compare (`PyException` has no `DecidableEq`). These helpers unwrap a
result into a `Bool` that `#guard` can check. They live here, rather than in either
test file, so the iterative and recursive test files can share them without one
importing the other.
-/

import Isqrt.Definitions.PythonOps

/-- True when the computation returned `.ok expected`. -/
def assertReturns (actual : Except PyException Int) (expected : Int) : Bool :=
  match actual with
  | .ok v => v == expected
  | .error _ => false

/-- True when the computation raised `ZeroDivisionError`. -/
def assertRaisesZeroDivisionError (actual : Except PyException Int) : Bool :=
  match actual with
  | .error .zeroDivisionError => true
  | _ => false

/-- True when the computation raised `ValueError msg`. -/
def assertRaisesValueError (msg : String) (actual : Except PyException Int) : Bool :=
  match actual with
  | .error (.valueError m) => m == msg
  | _ => false
