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

The goal of this module is to give a direct translation of the above Python code
into monadic Lean.

Key reference: https://lean-lang.org/papers/do.pdf
-/

/- Before we start, we'll need some way to model Python's exceptions. There are
   only two exceptions we need to worry about: ZeroDivisionError and ValueError

   That `deriving Repr` gives us a non-opaque way to see the contents of the exception
   when using #eval to print out the value of an expression. (Think of it as equivalent
   to supplying a `__repr__` method in Python.) -/

inductive PyException where
  | zeroDivisionError
  | valueError (msg: String)
deriving Repr

/- We'll use Lean's `Except` monad to represent the
   result of a function that could possibly raise. For example, the
   `Except PyException Int` type represents a function that either
   returns an integer or raises an exception. -/

/- We'll want some way to check the results that we get
  in tests. -/

def assertReturns (actual: Except PyException Int) (expected: Int) : Bool :=
  match actual with
  | Except.ok v => v == expected
  | Except.error _ => false


def assertRaisesZeroDivisionError (actual: Except PyException Int) : Bool :=
  match actual with
  | Except.ok _ => false
  | Except.error e =>
    match e with
    | PyException.zeroDivisionError => true
    | _ => false


def assertRaisesValueError (msg: String) (actual: Except PyException Int) : Bool :=
  match actual with
  | Except.ok _ => false
  | Except.error e =>
    match e with
    | PyException.valueError m => m == msg
    | _ => false


/- Now we can define pyFloordiv - the translation of Python's // operator for
   integer operands. -/

def pyFloordiv (a b : Int) : Except PyException Int :=
  if b = 0 then
    throw .zeroDivisionError
  else
    return Int.fdiv a b

/- Some checks that pyFloorDiv does the right thing. -/

#guard assertReturns (pyFloordiv 10 3) 3
#guard assertReturns (pyFloordiv 10 (-3)) (-4)
#guard assertReturns (pyFloordiv (-10) (-3)) 3
#guard assertReturns (pyFloordiv (-10) 3) (-4)
#guard assertRaisesZeroDivisionError (pyFloordiv 10 0)
#guard assertRaisesZeroDivisionError (pyFloordiv (-10) 0)
#guard assertRaisesZeroDivisionError (pyFloordiv 0 0)

/- Shift operations -/

def pyLshift (n k : Int) : Except PyException Int :=
  if k < 0 then
    throw (.valueError "negative shift count")
  else
    return n * (2 ^ k.toNat)


def pyRshift (n k : Int) : Except PyException Int :=
  if k < 0 then
    throw (.valueError "negative shift count")
  else
    return Int.fdiv n (2 ^ k.toNat)

/- Checks for the shift operations -/

#guard assertReturns (pyLshift 3 2) 12
#guard assertReturns (pyLshift 3 0) 3
#guard assertReturns (pyLshift (-3) 2) (-12)
#guard assertReturns (pyLshift (-3) 0) (-3)
#guard assertRaisesValueError "negative shift count" (pyLshift 3 (-1))

#guard assertReturns (pyRshift 12 3) 1
#guard assertReturns (pyRshift 12 2) 3
#guard assertReturns (pyRshift 12 0) 12
#guard assertReturns (pyRshift (-12) 3) (-2)
#guard assertReturns (pyRshift (-12) 2) (-3)
#guard assertReturns (pyRshift (-12) 0) (-12)
#guard assertRaisesValueError "negative shift count" (pyRshift 12 (-1))
#guard assertRaisesValueError "negative shift count" (pyRshift (-12) (-1))


/- Python's int.bit_length -/

def natBitLength : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.log2 (n + 1) + 1

def pyBitLength (n : Int) : Int := natBitLength n.natAbs

/- ... and tests for pyBitLength ... -/

#guard pyBitLength 0 = 0
#guard pyBitLength 1 = 1
#guard pyBitLength 2 = 2
#guard pyBitLength 1023 = 10
#guard pyBitLength 1024 = 11
#guard pyBitLength (-1023) = 10
#guard pyBitLength (-1024) = 11

/- Next up, an equivalent for single-argument `range`. We don't
   use Lean's `List.range` directly because that produces Nats,
   and we want to work with `Int`s throughout.

   Implementation note: `n.toNat` converts Int to Nat and conveniently maps negative
   values to 0. That gives us something which exactly matches Python's `range` behaviour
   for negative inputs (produce an empty list; don't raise).
   -/

def pyRange (n : Int) : List Int := (List.range n.toNat).map Int.ofNat

/- And tests. -/

#guard pyRange 0 == []
#guard pyRange 1 == [0]
#guard pyRange 5 == [0, 1, 2, 3, 4]
#guard pyRange (-5) == []


/- Now we can write isqrt. -/

def isqrt (n : Int) : Except PyException Int := do
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

/- Tests. -/

#guard assertReturns (isqrt 0) 0
#guard assertReturns (isqrt 1) 1
#guard assertReturns (isqrt 2) 1
#guard assertReturns (isqrt 3) 1
#guard assertReturns (isqrt 4) 2
#guard assertReturns (isqrt 5) 2
#guard assertReturns (isqrt 8) 2
#guard assertReturns (isqrt 9) 3
#guard assertReturns (isqrt 15) 3
#guard assertReturns (isqrt 16) 4
#guard assertReturns (isqrt 999999) 999
#guard assertReturns (isqrt 1000000) 1000
#guard assertReturns (isqrt (10^1000)) (10^500)
#guard assertRaisesValueError "isqrt() argument must be nonnegative" (isqrt (-1))

/- The assertion that a given value is a correct integer square root. -/

def isIntegerSquareRoot (n a : Int) : Prop :=
  a * a <= n ∧ n < (a + 1) * (a + 1)

/- The theorem we want to prove. -/

theorem isqrtCorrect (n : Int) :
    match (isqrt n) with
    | .ok a => 0 <= n ∧ isIntegerSquareRoot n a
    | .error e => n < 0 ∧ e = PyException.valueError "isqrt() argument must be nonnegative" := by sorry
