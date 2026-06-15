/-
The *recursive* integer square root in monadic (`Except`) form — the algorithm's
original derivation (CPython ships the iterative `isqrtIterative`). The algorithm:

    def isqrt_aux(c, n):
        if c == 0:
            return 1
        else:
            k = (c - 1) // 2
            a = isqrt_aux(c // 2, n >> (2 * k + 2))
            return (a << k) + (n >> (k + 2)) // a

    def isqrt(n):
        if n < 0:
            raise ValueError("isqrt() argument must be nonnegative")
        if n == 0:
            return 0
        else:
            c = (n.bit_length() - 1) // 2
            a = isqrt_aux(c, n)
            return a - 1 if n < a * a else a
-/

import Isqrt.Definitions.PythonPrimitives

/-- Recursive auxiliary computing a *near* square root of `n` — a value within one
of `⌊√n⌋`, which `isqrtRecursive` corrects with its final `a-1`/`a` step (hence
`nsqrt`). Structurally recursive on the counter `s`, called with `s = c.bit_length()`
so that `match s` reproduces `isqrt_aux`'s `if c == 0` base case. -/
def nsqrt (s : Nat) (c n : Int) : PyExcept Int :=
  match s with
  | 0 => pure 1
  | s + 1 => do
    let k ← pyFloordiv (c - 1) 2
    let cHalf ← pyFloordiv c 2
    let nShift ← pyRshift n (2 * k + 2)
    let a ← nsqrt s cHalf nShift
    let lsh ← pyLshift a k
    let rsh ← pyRshift n (k + 2)
    let q ← pyFloordiv rsh a
    pure (lsh + q)

/-- Integer square root of `n`, recursive monadic (`Except`) form — the direct
translation of the recursive Python listing above: raises `ValueError` for `n < 0`,
returns `0` for `n = 0`, otherwise computes `c`, calls `nsqrt` (counter seeded at
`c.bit_length()`), and applies the final `a-1`/`a` adjustment. -/
def isqrtRecursive (n : Int) : PyExcept Int := do
  if n < 0 then
    throw (.valueError "isqrt() argument must be nonnegative")
  if n = 0 then
    return 0

  let c ← pyFloordiv (pyBitLength n - 1) 2
  let a ← nsqrt (pyBitLength c).toNat c n
  return (if n < a * a then a - 1 else a)
