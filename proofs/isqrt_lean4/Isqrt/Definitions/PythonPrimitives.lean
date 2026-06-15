/-
Lean mirrors of the Python operations behind `math.isqrt`: floor division `//`,
left/right shift `<<`/`>>`, `range`, and `int.bit_length()`. The trust surface a
reader checks against Python.

`//`, `<<`, `>>` can raise, so they return `PyExcept`; `range` and `bit_length`
can't, so they're plain functions.
-/

import Isqrt.Definitions.Exceptions

/-- Python's `a // b` (floor division) as a `PyExcept`: raises `ZeroDivisionError`
when `b = 0`, otherwise returns `Int.fdiv a b` — which rounds toward `-∞`, matching
Python's `//` for every sign combination. -/
def pyFloordiv (a b : Int) : PyExcept Int :=
  if b = 0 then
    throw .zeroDivisionError
  else
    return Int.fdiv a b

/-- Python's `n << k` (left shift) as a `PyExcept`: raises `ValueError` on a
negative shift count, otherwise returns `n * 2 ^ k`. -/
def pyLshift (n k : Int) : PyExcept Int :=
  if k < 0 then
    throw (.valueError "negative shift count")
  else
    return n * (2 ^ k.toNat)

/-- Python's `n >> k` (right shift) as a `PyExcept`: raises `ValueError` on a
negative shift count, otherwise returns `Int.fdiv n (2 ^ k)` (floor division by
`2 ^ k`). -/
def pyRshift (n k : Int) : PyExcept Int :=
  if k < 0 then
    throw (.valueError "negative shift count")
  else
    return Int.fdiv n (2 ^ k.toNat)

/-- Python's single-argument `range(n)` as a list of `Int`s. `n.toNat` maps
negative `n` to `0`, exactly matching Python's "empty range, no error" behaviour
for nonpositive arguments. -/
def pyRange (n : Int) : List Int := (List.range n.toNat).map Int.ofNat

/-- Python's `n.bit_length()`: the number of bits needed to represent `abs(n)`,
with `(0).bit_length() == 0`. Computed via `Nat.log2` on `n.natAbs`, matching
`⌊log2 n⌋ + 1` for `n > 0`. -/
def pyBitLength (n : Int) : Int :=
  ↑(match n.natAbs with
    | 0 => 0
    | m + 1 => Nat.log2 (m + 1) + 1)
