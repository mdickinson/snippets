/-
Direct actual-equals-expected-style tests for the Python primitives used by the `isqrt`
implementations.
-/

module

meta import Isqrt.Definitions.PythonPrimitives
meta import Isqrt.Tests.Assertions

open scoped Python

/-! ## Floor division -/

#guard assertReturns (10 // 3) 3
#guard assertReturns (10 // (-3)) (-4)
#guard assertReturns ((-10) // (-3)) 3
#guard assertReturns ((-10) // 3) (-4)
#guard assertRaisesZeroDivisionError (10 // 0)
#guard assertRaisesZeroDivisionError ((-10) // 0)
#guard assertRaisesZeroDivisionError (0 // 0)

/-! ## Left shift -/

#guard assertReturns (3 << 2) 12
#guard assertReturns (3 << 0) 3
#guard assertReturns ((-3) << 2) (-12)
#guard assertReturns ((-3) << 0) (-3)
#guard assertRaisesValueError "negative shift count" (3 << (-1))
#guard assertRaisesValueError "negative shift count" ((-3) << (-1))

/-! ## Right shift -/

#guard assertReturns (12 >> 3) 1
#guard assertReturns (12 >> 2) 3
#guard assertReturns (12 >> 0) 12
#guard assertReturns ((-12) >> 3) (-2)
#guard assertReturns ((-12) >> 2) (-3)
#guard assertReturns ((-12) >> 0) (-12)
#guard assertRaisesValueError "negative shift count" (12 >> (-1))
#guard assertRaisesValueError "negative shift count" ((-12) >> (-1))

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
