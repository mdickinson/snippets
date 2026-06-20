/-
Direct actual-equals-expected-style tests for the Python primitives used by the `isqrt`
implementations.
-/

module

meta import Isqrt.Definitions.PythonPrimitives
meta import Isqrt.Tests.Assertions

/-! ## pyFloordiv -/

#guard assertReturns (pyFloordiv 10 3) 3
#guard assertReturns (pyFloordiv 10 (-3)) (-4)
#guard assertReturns (pyFloordiv (-10) (-3)) 3
#guard assertReturns (pyFloordiv (-10) 3) (-4)
#guard assertRaisesZeroDivisionError (pyFloordiv 10 0)
#guard assertRaisesZeroDivisionError (pyFloordiv (-10) 0)
#guard assertRaisesZeroDivisionError (pyFloordiv 0 0)

/-! ## pyLshift -/

#guard assertReturns (pyLshift 3 2) 12
#guard assertReturns (pyLshift 3 0) 3
#guard assertReturns (pyLshift (-3) 2) (-12)
#guard assertReturns (pyLshift (-3) 0) (-3)
#guard assertRaisesValueError "negative shift count" (pyLshift 3 (-1))
#guard assertRaisesValueError "negative shift count" (pyLshift (-3) (-1))

/-! ## pyRshift -/

#guard assertReturns (pyRshift 12 3) 1
#guard assertReturns (pyRshift 12 2) 3
#guard assertReturns (pyRshift 12 0) 12
#guard assertReturns (pyRshift (-12) 3) (-2)
#guard assertReturns (pyRshift (-12) 2) (-3)
#guard assertReturns (pyRshift (-12) 0) (-12)
#guard assertRaisesValueError "negative shift count" (pyRshift 12 (-1))
#guard assertRaisesValueError "negative shift count" (pyRshift (-12) (-1))

/-! ## range -/

#guard range 0 == []
#guard range 1 == [0]
#guard range 5 == [0, 1, 2, 3, 4]
#guard range (-5) == []

/-! ## Int.bitLength -/

#guard Int.bitLength 0 == 0
#guard Int.bitLength 1 == 1
#guard Int.bitLength 255 == 8
#guard Int.bitLength 256 == 9
#guard Int.bitLength (10^1000) == 3322
#guard Int.bitLength (-256) == 9             -- bit_length of abs
