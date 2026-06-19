/-
Lean equivalents of Python's <<, >>, //, range and int.bit_length(), with
the same exception-raising behaviour as in Python.
-/

import Isqrt.Definitions.Exceptions

/-- The floor of a / b, raising zeroDivisionError if b = 0. -/
def pyFloordiv (a b : Int) : PyExcept Int :=
  if b = 0 then
    throw <| .zeroDivisionError "division by zero"
  else
    return Int.fdiv a b

/-- Equivalent of Python's n << k, raising valueError if k is negative. -/
def pyLshift (n k : Int) : PyExcept Int :=
  if k < 0 then
    throw <| .valueError "negative shift count"
  else
    return n <<< k.toNat

/-- Equivalent of Python's n >> k, raising valueError if k is negative. -/
def pyRshift (n k : Int) : PyExcept Int :=
  if k < 0 then
    throw <| .valueError "negative shift count"
  else
    return n >>> k.toNat

/-- Integers from 0 (inclusive) to n (exclusive); empty list if n is negative. -/
def range (n : Int) : List Int := (List.range n.toNat).map Int.ofNat

/--
Equivalent of Python's int.bit_length - the minimum number of bits needed
to represent abs(n) - with `Int.bitLength 0 = 0`.
-/
def Int.bitLength (n : Int) : Int := if n = 0 then 0 else Nat.log2 n.natAbs + 1
