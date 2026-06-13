/-
Sanity checks for the *recursive* monadic (`Except`) integer square root
`isqrtRecExcept`. These mirror the `isqrtExcept` checks in
`Isqrt.Tests.MonadicIsqrt`, reusing its `assert*` helpers. A failing `#guard`
causes a build error.
-/

import Isqrt.RecursiveExcept
import Isqrt.Tests.MonadicIsqrt

/-! ## isqrtRecExcept -/

#guard assertReturns (isqrtRecExcept 0) 0
#guard assertReturns (isqrtRecExcept 1) 1
#guard assertReturns (isqrtRecExcept 2) 1
#guard assertReturns (isqrtRecExcept 3) 1
#guard assertReturns (isqrtRecExcept 4) 2
#guard assertReturns (isqrtRecExcept 5) 2
#guard assertReturns (isqrtRecExcept 8) 2
#guard assertReturns (isqrtRecExcept 9) 3
#guard assertReturns (isqrtRecExcept 15) 3
#guard assertReturns (isqrtRecExcept 16) 4
#guard assertReturns (isqrtRecExcept 999999) 999
#guard assertReturns (isqrtRecExcept 1000000) 1000
#guard assertReturns (isqrtRecExcept (10 ^ 1000)) (10 ^ 500)
#guard assertRaisesValueError "isqrt() argument must be nonnegative" (isqrtRecExcept (-1))
