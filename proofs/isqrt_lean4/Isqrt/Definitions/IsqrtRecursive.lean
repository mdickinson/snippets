/-
Lean translation of the recursive form of the CPython `isqrt` algorithm.

Here's the algorithm expressed recursively in Python. The core function `nsqrt`
recursively computes a (positive) "near square root" of a positive integer `n`; the
outer `isqrt` function deals with negative and zero inputs and for positive `n` applies
the final correction to the near square root (if necessary) to turn it into the integer
square root.

    def nsqrt(n: int, c: int) -> int:
        """Recursively compute a near square root of a positive integer n."""
        if c == 0:
            return 1
        else:
            k = (c - 1) // 2
            a = nsqrt(n >> 2 * k + 2, c // 2)
            return (a << k) + (n >> k + 2) // a

    def isqrt(n: int) -> int:
        """Return the integer part of the square root of the input."""
        if n < 0:
            raise ValueError("isqrt() argument must be nonnegative")
        if n == 0:
            return 0

        a = nsqrt(n, (n.bit_length() - 1) // 2)

        return a - 1 if n < a * a else a

There's a barrier to a direct translation of the above code. By default Lean requires
functions to be total, and our Python `nsqrt` isn't: `nsqrt` will recurse infinitely for
negative `c`. To fix that we introduce an explicit loop counter, `s`, with `s =
c.bit_length()` throughout the recursion. So the actual code that we'll translate looks
like this:

    def nsqrt(n: int, c: int, s: int) -> int:
        """Recursively compute a near square root of a positive integer n."""
        if s == 0:
            return 1
        else:
            k = (c - 1) // 2
            a = nsqrt(n >> 2 * k + 2, c // 2, s - 1)
            return (a << k) + (n >> k + 2) // a

    def isqrt(n: int) -> int:
        """Return the integer part of the square root of the input."""
        if n < 0:
            raise ValueError("isqrt() argument must be nonnegative")
        if n == 0:
            return 0

        c = (n.bit_length() - 1) // 2
        a = nsqrt(n, c, c.bit_length())

        return a - 1 if n < a * a else a

This Python code now clearly terminates provided that the input `s` is nonnegative; for
negative `s` it still enters an unbounded recursion. In the Lean translation,
nonnegativity of `s` is enforced by using type `Nat` instead of `Int` for `s`, and Lean
can then deduce automatically that the recursion terminates.
-/

import Isqrt.Definitions.Exceptions
import Isqrt.Definitions.PythonPrimitives

/-
Infix aliases for the Python operations, with precedence chosen to match that of Python.
We bump the priority of `>>` to avoid a clash with the monadic `>>` operator.
-/

local infixl:70 "//" => pyFloordiv
local infixl:62 "<<" => pyLshift
local infixl:62 (priority := high) ">>" => pyRshift

/-- Return a near square root of a positive integer n. -/
def nsqrtRecursive (n c : Int) (s : Nat) : PyExcept Int := do
  if s = 0 then
    return 1
  else
    let k ← (c - 1) // 2
    let a ← nsqrtRecursive (← n >> 2 * k + 2) (← c // 2) (s - 1)
    return (← a << k) + (← (← n >> k + 2) // a)

/-- Return the integer part of the square root of the input. -/
def isqrtRecursive (n : Int) : PyExcept Int := do
  if n < 0 then
    throw <| .valueError "isqrt() argument must be nonnegative"
  if n = 0 then
    return 0

  let c ← (n.bitLength - 1) // 2
  let a ← nsqrtRecursive n c c.bitLength.toNat

  return if n < a * a then a - 1 else a
