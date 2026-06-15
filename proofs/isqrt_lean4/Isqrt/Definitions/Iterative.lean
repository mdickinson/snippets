/-
The *iterative* integer square root in monadic (`Except`) form — the formulation
CPython ships. The C source gives the equivalent Python in a comment, reproduced
verbatim here:

    def isqrt(n):
        """
        Return the integer part of the square root of the input.
        """
        n = operator.index(n)

        if n < 0:
            raise ValueError("isqrt() argument must be nonnegative")
        if n == 0:
            return 0

        c = (n.bit_length() - 1) // 2
        a = 1
        d = 0
        for s in reversed(range(c.bit_length())):
            # Loop invariant: (a-1)**2 < (n >> 2*(c - d)) < (a+1)**2
            e = d
            d = c >> s
            a = (a << d - e - 1) + (n >> 2*c - e - d + 1) // a

        return a - (a*a > n)
-/

import Isqrt.Definitions.PythonOps

/-- Integer square root of `n`, monadic (`Except`) form — the direct `do`-block
translation of the Python listing above: raises `ValueError` for `n < 0`, returns
`0` for `n = 0`, otherwise runs the loop carrying the running approximation `a` and
previous shift `d` as `let mut` state, and returns `a - (if a*a > n then 1 else 0)`
(Python's `a - (a*a > n)`, bool-to-int spelled out). -/
def isqrtIterative (n : Int) : PyExcept Int := do
  if n < 0 then
    throw (.valueError "isqrt() argument must be nonnegative")
  if n = 0 then
    return 0

  let c ← pyFloordiv (pyBitLength n - 1) 2
  let mut a := (1 : Int)
  let mut d := (0 : Int)
  for s in (pyRange (pyBitLength c)).reverse do
    let e := d
    d := (← pyRshift c s)
    a := (← pyLshift a (d - e - 1)) + (← pyFloordiv (← pyRshift n (2 * c - e - d + 1)) a)

  return a - (if a * a > n then 1 else 0)
