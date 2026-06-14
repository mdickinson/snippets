/-
Sanity checks for the *recursive* monadic (`Except`) integer square root
`isqrt`. These mirror the `isqrtIterative` checks in `Isqrt.Tests.Iterative`,
using the shared `assert*` helpers of `Isqrt.Tests.Assertions`. A failing
`#guard` causes a build error.
-/

import Isqrt.Definitions.Algorithm
import Isqrt.Tests.Assertions

/-! ## isqrt -/

#guard assertReturns (isqrt 0) 0
#guard assertReturns (isqrt 1) 1
#guard assertReturns (isqrt 2) 1
#guard assertReturns (isqrt 3) 1
#guard assertReturns (isqrt 4) 2
#guard assertReturns (isqrt 5) 2
#guard assertReturns (isqrt 8) 2
#guard assertReturns (isqrt 9) 3
#guard assertReturns (isqrt 15) 3
#guard assertReturns (isqrt 16) 4
#guard assertReturns (isqrt 24) 4            -- just below 5² = 25
#guard assertReturns (isqrt 25) 5            -- perfect square
#guard assertReturns (isqrt 26) 5            -- just above 5²
#guard assertReturns (isqrt 999999) 999
#guard assertReturns (isqrt 1000000) 1000
#guard assertReturns (isqrt 1000001) 1000    -- just above 1000²
#guard assertReturns (isqrt (10 ^ 1000)) (10 ^ 500)
#guard assertRaisesValueError "isqrt() argument must be nonnegative" (isqrt (-1))
