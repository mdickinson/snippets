module

meta import LimitDenominator.Definitions.PythonPrimitives
meta import LimitDenominator.Tests.Assertions

/-!
Tests pinning down the Python primitives, including the sign conventions of `//` and `%` that
`Int.fdiv` and `Int.fmod` are chosen to match, and the short-circuiting of `and`.

The expected values were all checked against CPython.
-/

open scoped Python

/-! ## Floor division and modulus, over every combination of signs -/

#guard assertReturns (pyFloordiv 7 2) 3
#guard assertReturns (pyFloordiv 7 (-2)) (-4)
#guard assertReturns (pyFloordiv (-7) 2) (-4)
#guard assertReturns (pyFloordiv (-7) (-2)) 3

#guard assertReturns (pyMod 7 2) 1
#guard assertReturns (pyMod 7 (-2)) (-1)
#guard assertReturns (pyMod (-7) 2) 1
#guard assertReturns (pyMod (-7) (-2)) (-1)

#guard assertReturns (pyFloordiv 0 5) 0
#guard assertReturns (pyMod 0 5) 0

#guard assertRaisesZeroDivisionError (pyFloordiv 7 0)
#guard assertRaisesZeroDivisionError (pyMod 7 0)

/-! ## The notation agrees with the underlying primitives -/

#guard assertReturns (7 // 2 : PyExcept Int) 3
#guard assertReturns (7 % 2 : PyExcept Int) 1

/-! ## `and` short-circuits: a false left operand never runs the right one -/

#guard assertReturns (pure false <&&> (do let _ ← pyFloordiv 1 0; return true)) false
#guard assertRaisesZeroDivisionError (pure true <&&> (do let _ ← pyFloordiv 1 0; return true))
#guard assertReturns (pure true <&&> (pure true : PyExcept Bool)) true
#guard assertReturns (pure true <&&> (pure false : PyExcept Bool)) false
