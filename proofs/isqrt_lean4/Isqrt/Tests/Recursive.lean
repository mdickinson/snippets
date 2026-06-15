/-
Sanity checks for the *recursive* monadic (`Except`) integer square root
`isqrtRecursive`. These mirror the `isqrtIterative` checks in `Isqrt.Tests.Iterative`,
using the shared `assert*` helpers of `Isqrt.Tests.Assertions`. A failing
`#guard` causes a build error.
-/

import Isqrt.Definitions.IsqrtRecursive
import Isqrt.Tests.Assertions

/-! ## isqrtRecursive -/

#guard assertReturns (isqrtRecursive 0) 0
#guard assertReturns (isqrtRecursive 1) 1
#guard assertReturns (isqrtRecursive 2) 1
#guard assertReturns (isqrtRecursive 3) 1
#guard assertReturns (isqrtRecursive 4) 2
#guard assertReturns (isqrtRecursive 5) 2
#guard assertReturns (isqrtRecursive 8) 2
#guard assertReturns (isqrtRecursive 9) 3
#guard assertReturns (isqrtRecursive 15) 3
#guard assertReturns (isqrtRecursive 16) 4
#guard assertReturns (isqrtRecursive 24) 4            -- just below 5² = 25
#guard assertReturns (isqrtRecursive 25) 5            -- perfect square
#guard assertReturns (isqrtRecursive 26) 5            -- just above 5²
#guard assertReturns (isqrtRecursive 999999) 999
#guard assertReturns (isqrtRecursive 1000000) 1000
#guard assertReturns (isqrtRecursive 1000001) 1000    -- just above 1000²
#guard assertReturns (isqrtRecursive (10 ^ 1000)) (10 ^ 500)
#guard assertRaisesValueError "isqrt() argument must be nonnegative" (isqrtRecursive (-1))
