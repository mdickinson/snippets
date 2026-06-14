/-
The *recursive* integer square root, in monadic (`Except`) form — the companion
to the iterative `isqrtIterative` of `Isqrt.Definitions.Iterative`. The recursive
algorithm, again taken verbatim from the comments in CPython's `math.isqrt` C source:

    def isqrt_aux(c, n):
        if c == 0:
            return 1
        else:
            k = (c - 1) // 2
            a = isqrt_aux(c // 2, n >> (2 * k + 2))
            return (a << k) + (n >> (k + 2)) // a

    def isqrt(n):
        if n == 0:
            return 0
        else:
            c = (n.bit_length() - 1) // 2
            a = isqrt_aux(c, n)
            return a - 1 if n < a * a else a

As with the iterative translation, the operations that can raise (`//`, `>>`,
`<<`) become the `Except`-returning `pyFloordiv` / `pyRshift` /
`pyLshift`, so every line that could raise in Python is a monadic bind `←`.

The one structural wrinkle: `isqrt_aux` recurses on `c // 2` with `c == 0` as its
base case, but a *monadic* `c // 2` is bind-opaque to Lean's termination checker
(and `(-1) // 2 = -1` in Python, so a verbatim translation would even self-loop on
`c < 0`). We sidestep both by recursing **structurally on an explicit counter**
`s : Nat`, seeded at `c.bit_length()`. Since `(c // 2).bit_length() = c.bit_length() - 1`
for `c > 0` (`Isqrt.Proofs.BitLengthLemmas.toNat_pyBitLength_fdiv_two`), the counter
decreases by exactly one per recursive step and hits `0` precisely when `c` does —
so `match s` faithfully reproduces the `if c == 0` base case with no `termination_by`,
no precondition, and `c // 2` left as a genuine `Except` operation. The same counter
is CPython's *iterative* loop bound `reversed(range(c.bit_length()))`, so the two
formulations share a skeleton.

Correctness is proved in `Isqrt.Proofs.Correctness`.
-/

import Isqrt.Definitions.PythonOps
import Isqrt.Definitions.BitLength

/-- Recursive auxiliary for the monadic integer square root, structurally
recursive on the counter `s`. Intended to be called with `s = c.bit_length()`;
under that invariant the `match s` reproduces `isqrt_aux`'s `if c == 0` base case.
Each `←` binds an operation that could raise; the correctness proof shows none of
them ever does when `s = c.bit_length()` and `c ≥ 0`. -/
def isqrtAux (s : Nat) (c n : Int) : Except PyException Int :=
  match s with
  | 0 => pure 1
  | s + 1 => do
    let k ← pyFloordiv (c - 1) 2
    let cHalf ← pyFloordiv c 2
    let nShift ← pyRshift n (2 * k + 2)
    let a ← isqrtAux s cHalf nShift
    let lsh ← pyLshift a k
    let rsh ← pyRshift n (k + 2)
    let q ← pyFloordiv rsh a
    pure (lsh + q)

/-- Integer square root of `n`, recursive monadic (`Except`) form — the direct
translation of the recursive CPython source above.

For `n < 0` it raises `ValueError`; for `n = 0` it returns `0`; otherwise it
computes `c = (n.bit_length() - 1) // 2`, calls `isqrtAux` with the
structural counter seeded at `c.bit_length()`, and applies the final `a-1`/`a`
adjustment. Correctness is `Isqrt.Proofs.Correctness`. -/
def isqrt (n : Int) : Except PyException Int := do
  if n < 0 then
    throw (.valueError "isqrt() argument must be nonnegative")
  if n = 0 then
    return 0

  let c ← pyFloordiv (pyBitLength n - 1) 2
  let a ← isqrtAux (pyBitLength c).toNat c n
  return (if n < a * a then a - 1 else a)
