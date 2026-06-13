/-
Sanity checks for the monadic (`Except`) integer square root `isqrtExcept` and
the `Except`-returning Python operations it uses. These mirror the concrete-value
checks in `Isqrt.Tests.Isqrt` / `Isqrt.Tests.PythonOps`, adapted to `Except`
results via the `assert*` helpers below. A failing `#guard` causes a build error.
-/

import Isqrt.MonadicIsqrt

/-! ## Assertion helpers for `Except PyException Int` results -/

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

/-! ## pyFloordivExcept -/

#guard assertReturns (pyFloordivExcept 10 3) 3
#guard assertReturns (pyFloordivExcept 10 (-3)) (-4)
#guard assertReturns (pyFloordivExcept (-10) (-3)) 3
#guard assertReturns (pyFloordivExcept (-10) 3) (-4)
#guard assertRaisesZeroDivisionError (pyFloordivExcept 10 0)
#guard assertRaisesZeroDivisionError (pyFloordivExcept (-10) 0)
#guard assertRaisesZeroDivisionError (pyFloordivExcept 0 0)

/-! ## pyLshiftExcept / pyRshiftExcept -/

#guard assertReturns (pyLshiftExcept 3 2) 12
#guard assertReturns (pyLshiftExcept 3 0) 3
#guard assertReturns (pyLshiftExcept (-3) 2) (-12)
#guard assertReturns (pyLshiftExcept (-3) 0) (-3)
#guard assertRaisesValueError "negative shift count" (pyLshiftExcept 3 (-1))

#guard assertReturns (pyRshiftExcept 12 3) 1
#guard assertReturns (pyRshiftExcept 12 2) 3
#guard assertReturns (pyRshiftExcept 12 0) 12
#guard assertReturns (pyRshiftExcept (-12) 3) (-2)
#guard assertReturns (pyRshiftExcept (-12) 2) (-3)
#guard assertReturns (pyRshiftExcept (-12) 0) (-12)
#guard assertRaisesValueError "negative shift count" (pyRshiftExcept 12 (-1))
#guard assertRaisesValueError "negative shift count" (pyRshiftExcept (-12) (-1))

/-! ## pyRange -/

#guard pyRange 0 == []
#guard pyRange 1 == [0]
#guard pyRange 5 == [0, 1, 2, 3, 4]
#guard pyRange (-5) == []

/-! ## isqrtExcept -/

#guard assertReturns (isqrtExcept 0) 0
#guard assertReturns (isqrtExcept 1) 1
#guard assertReturns (isqrtExcept 2) 1
#guard assertReturns (isqrtExcept 3) 1
#guard assertReturns (isqrtExcept 4) 2
#guard assertReturns (isqrtExcept 5) 2
#guard assertReturns (isqrtExcept 8) 2
#guard assertReturns (isqrtExcept 9) 3
#guard assertReturns (isqrtExcept 15) 3
#guard assertReturns (isqrtExcept 16) 4
#guard assertReturns (isqrtExcept 999999) 999
#guard assertReturns (isqrtExcept 1000000) 1000
#guard assertReturns (isqrtExcept (10 ^ 1000)) (10 ^ 500)
#guard assertRaisesValueError "isqrt() argument must be nonnegative" (isqrtExcept (-1))
