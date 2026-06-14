/-

Python's `math` module defines an `isqrt` function that computes the integer
part of the square root of a nonnegative integer input. The implementation of
`math.isqrt` is in C, but the comments in the C source include equivalent
Python code, reproduced verbatim here for easy reference.

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

This module gives a direct translation of the above Python into *monadic* Lean:
the operations that can raise (`//`, `>>`, `<<`) become the `Except`-returning
`pyFloordiv` / `pyRshift` / `pyLshift` of `Isqrt.Definitions.PythonOps`,
and `isqrt` itself is a `do` block — `let mut a/d`, a `for … in`, and monadic binds
(`←`) for each operation that could raise. The function is named `isqrtIterative`
to set it apart from the recursive `isqrt` of `Isqrt.Definitions.Algorithm`: the two
are the iterative and recursive translations of the same CPython algorithm, sharing
the operators of `Isqrt.Definitions.PythonOps` and `pyBitLength` of
`Isqrt.Definitions.BitLength`.

Correctness is proved in `Isqrt.Proofs.IterativeCorrectness`.

Key reference: https://lean-lang.org/papers/do.pdf
-/

import Isqrt.Definitions.PythonOps
import Isqrt.Definitions.BitLength

/-- Integer square root of `n`, monadic (`Except`) form — the direct `do`-block
translation of the CPython source above.

For `n < 0` it raises `ValueError`; for `n = 0` it returns `0`; otherwise it runs
the `for s in reversed(range(c.bit_length()))` loop, carrying the running
approximation `a` and the previous shift `d` as `let mut` state, and returns
`a - (if a*a > n then 1 else 0)` (Python's `a - (a*a > n)`, with the implicit
bool-to-int spelled out). Each `←` binds an operation that could raise; the
correctness proof shows none of them ever does for `n ≥ 0`. -/
def isqrtIterative (n : Int) : Except PyException Int := do
  if n < 0 then
    throw (.valueError "isqrt() argument must be nonnegative")
  if n = 0 then
    return 0

  let c := <- pyFloordiv (pyBitLength n - 1) 2
  let mut a := (1 : Int)
  let mut d := (0 : Int)
  for s in (pyRange (pyBitLength c)).reverse do
    let e := d
    d := (<- pyRshift c s)
    a := (<- pyLshift a (d - e - 1)) + (<- pyFloordiv (<- pyRshift n (2 * c - e - d + 1)) a)

  return a - (if a * a > n then 1 else 0)
