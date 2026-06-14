/-
Sanity checks for the iterative integer square root `isqrtIterative` and the
Python operations it uses: the `Except`-returning `pyFloordiv` / `pyLshift` /
`pyRshift` / `pyRange`, plus the plain `pyBitLength`. The `Except` results run
through the `assert*` helpers of `Isqrt.Tests.Assertions`, which unwrap an
`Except PyException Int` — a bare `#guard` cannot, since `PyException` has no
`DecidableEq`; `pyBitLength` returns a plain `Int`, so it is checked with `#guard`
directly. A failing `#guard` causes a build error.
-/

import Isqrt.Definitions.Iterative
import Isqrt.Tests.Assertions

/-! ## pyFloordiv -/

#guard assertReturns (pyFloordiv 10 3) 3
#guard assertReturns (pyFloordiv 10 (-3)) (-4)
#guard assertReturns (pyFloordiv (-10) (-3)) 3
#guard assertReturns (pyFloordiv (-10) 3) (-4)
#guard assertRaisesZeroDivisionError (pyFloordiv 10 0)
#guard assertRaisesZeroDivisionError (pyFloordiv (-10) 0)
#guard assertRaisesZeroDivisionError (pyFloordiv 0 0)

/-! ## pyLshift / pyRshift -/

#guard assertReturns (pyLshift 3 2) 12
#guard assertReturns (pyLshift 3 0) 3
#guard assertReturns (pyLshift (-3) 2) (-12)
#guard assertReturns (pyLshift (-3) 0) (-3)
#guard assertRaisesValueError "negative shift count" (pyLshift 3 (-1))

#guard assertReturns (pyRshift 12 3) 1
#guard assertReturns (pyRshift 12 2) 3
#guard assertReturns (pyRshift 12 0) 12
#guard assertReturns (pyRshift (-12) 3) (-2)
#guard assertReturns (pyRshift (-12) 2) (-3)
#guard assertReturns (pyRshift (-12) 0) (-12)
#guard assertRaisesValueError "negative shift count" (pyRshift 12 (-1))
#guard assertRaisesValueError "negative shift count" (pyRshift (-12) (-1))

/-! ## pyRange -/

#guard pyRange 0 == []
#guard pyRange 1 == [0]
#guard pyRange 5 == [0, 1, 2, 3, 4]
#guard pyRange (-5) == []

/-! ## pyBitLength -/

#guard pyBitLength 0 == 0
#guard pyBitLength 1 == 1
#guard pyBitLength 255 == 8
#guard pyBitLength 256 == 9
#guard pyBitLength (-256) == 9               -- bit_length of abs

/-! ## isqrtIterative -/

#guard assertReturns (isqrtIterative 0) 0
#guard assertReturns (isqrtIterative 1) 1
#guard assertReturns (isqrtIterative 2) 1
#guard assertReturns (isqrtIterative 3) 1
#guard assertReturns (isqrtIterative 4) 2
#guard assertReturns (isqrtIterative 5) 2
#guard assertReturns (isqrtIterative 8) 2
#guard assertReturns (isqrtIterative 9) 3
#guard assertReturns (isqrtIterative 15) 3
#guard assertReturns (isqrtIterative 16) 4
#guard assertReturns (isqrtIterative 999999) 999
#guard assertReturns (isqrtIterative 1000000) 1000
#guard assertReturns (isqrtIterative (10 ^ 1000)) (10 ^ 500)
#guard assertRaisesValueError "isqrt() argument must be nonnegative" (isqrtIterative (-1))
