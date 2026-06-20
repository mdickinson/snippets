/-
Lean equivalents of Python's <<, >>, //, range and int.bit_length(), with
the same exception-raising behaviour as in Python.
-/

module

public import Isqrt.Definitions.Exceptions

@[expose] public section

/-- The floor of a / b, raising zeroDivisionError if b = 0. -/
def pyFloordiv (a b : Int) : PyExcept Int := do
  if b = 0 then throw <| .zeroDivisionError "division by zero"
  return Int.fdiv a b

/-- Equivalent of Python's n << k, raising valueError if k is negative. -/
def pyLshift (n k : Int) : PyExcept Int := do
  if k < 0 then throw <| .valueError "negative shift count"
  return n <<< k.toNat

/-- Equivalent of Python's n >> k, raising valueError if k is negative. -/
def pyRshift (n k : Int) : PyExcept Int := do
  if k < 0 then throw <| .valueError "negative shift count"
  return n >>> k.toNat

/-- Integers from 0 (inclusive) to n (exclusive); empty list if n is negative. -/
def range (n : Int) : List Int := (List.range n.toNat).map Int.ofNat

/-- Minimum number of bits needed to represent abs(n). -/
def Int.bitLength (n : Int) : Int := if n = 0 then 0 else Nat.log2 n.natAbs + 1

end
