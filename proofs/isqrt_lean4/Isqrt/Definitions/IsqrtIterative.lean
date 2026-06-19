/-
Translation of the Python `isqrt` code in iterative form into Lean. Here's the Python
code we'll translate:

    def isqrt(n : int) -> int:
        """Return the integer part of the square root of the input."""
        if n < 0:
            raise ValueError("isqrt() argument must be nonnegative")
        if n == 0:
            return 0

        c = (n.bit_length() - 1) // 2
        a = 1
        d = 0
        for s in reversed(range(c.bit_length())):
            e = d
            d = c >> s
            a = (a << d - e - 1) + (n >> 2*c - e - d + 1) // a

        return a - (a*a > n)
-/

import Isqrt.Definitions.Exceptions
import Isqrt.Definitions.PythonPrimitives

/-
A bit of local syntactic sugar: infix aliases for the Python operations.
We bump the priority of `>>` to avoid a clash with the monadic `>>` operator.
-/

local infixl:70 "//" => pyFloordiv
local infixl:60 "<<" => pyLshift
local infixl:60 (priority := high) ">>" => pyRshift

/-- Return the integer part of the square root of the input. -/
def isqrtIterative (n : Int) : PyExcept Int := do
  if n < 0 then
    throw <| .valueError "isqrt() argument must be nonnegative"
  if n = 0 then
    return 0

  let c ← (pyBitLength n - 1) // 2
  let mut a := 1
  let mut d := 0
  for s in (pyRange (pyBitLength c)).reverse do
    let e := d
    d ← c >> s
    a := (← a << (d - e - 1)) + (← (← (n >> (2 * c - e - d + 1))) // a)

  return a - (if a * a > n then 1 else 0)
