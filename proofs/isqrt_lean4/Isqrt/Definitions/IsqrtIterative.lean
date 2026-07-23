/-
Lean translation of the iterative form of the CPython `isqrt` algorithm.

Here's the Python code that we'll translate. It's been tweaked slightly from the Python
code that's in comments in the CPython source, but the equivalency with that version
should be self-evident.

    def isqrt(n: int) -> int:
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
            a = (a << d - e - 1) + (n >> 2 * c - e - d + 1) // a

        return a - 1 if n < a * a else a
-/

module

public import Isqrt.Definitions.Exceptions
public import Isqrt.Definitions.PythonPrimitives

@[expose] public section

open scoped Python

/-- Return the integer part of the square root of the input. -/
def isqrtIterative (n : Int) : PyExcept Int := do
  if n < 0 then
    throw <| .valueError "isqrt() argument must be nonnegative"
  if n = 0 then
    return 0

  let c ← (n.bitLength - 1) // 2
  let mut a := 1
  let mut d := 0
  for s in List.reverse (range c.bitLength) do
    let e := d
    d ← c >> s
    a := (← a << d - e - 1) + (← (← n >> 2 * c - e - d + 1) // a)

  return if n < a * a then a - 1 else a

end
