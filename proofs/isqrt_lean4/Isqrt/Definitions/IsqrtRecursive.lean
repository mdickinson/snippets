/-
Lean translation of the recursive form of the CPython `isqrt` algorithm.

Here's the algorithm expressed recursively in Python. The inner `nsqrt` function
recursively computes a (positive) "near square root" of a positive integer `n`; the
outer `isqrt` function peels off the negative and zero cases, hands off to `nsqrt`,
and then corrects the resulting near square root if necessary.

    def nsqrt(n: int, c: int) -> int:
        """Recursively compute a near square root of a positive integer n."""
        if c <= 0:
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

There are two barriers to a direct translation of the above code into Lean. First, we
have to convince Lean that `nsqrt` terminates. We do that by providing a `Nat`-valued
measure for the recursion along with a proof that that measure strictly decreases on
each recursive call. The measure we choose is simply `c.toNat` - i.e., `max(c, 0)`
considered as a natural number.

The second inconvenience is that we can't use the `← c // 2` notation that we'd like to
use in the recursive call, because Lean can't surface the wrapped `Int` value for use in
the proof that the measure decreases. So we accept a slight loss of fidelity with
respect to the Python code and use the equivalent `c.fdiv 2` instead.
-/

module

public import Isqrt.Definitions.Exceptions
public import Isqrt.Definitions.PythonPrimitives

@[expose] public section

/-
Infix aliases for the Python operations, with precedence chosen to match that of Python.
We bump the priority of `>>` to avoid a clash with the monadic `>>` operator.
-/

local infixl:70 "//" => pyFloordiv
local infixl:62 "<<" => pyLshift
local infixl:62 (priority := high) ">>" => pyRshift

/-- Statement that our chosen measure decreases. -/
theorem Int.toNat_fdiv_two_lt {c : Int} (hc : ¬c <= 0) : (c.fdiv 2).toNat < c.toNat := by
  rw [Int.fdiv_eq_ediv_of_nonneg c (by decide)]
  apply (Int.toNat_lt_toNat (Int.lt_of_not_ge hc)).mpr ((Int.ediv_lt_of_lt_mul (by decide) _))
  rw [Int.mul_comm, Int.two_mul]
  exact Int.lt_add_of_le_of_pos (c.le_refl) (Int.lt_of_not_ge hc)

/-- Return a near square root of a positive integer n. -/
def nsqrtRecursive (n c : Int) : PyExcept Int := do
  if c <= 0 then
    return 1
  else
    let k ← (c - 1) // 2
    let a ← nsqrtRecursive (← n >> 2 * k + 2) (c.fdiv 2)
    return (← a << k) + (← (← n >> k + 2) // a)
termination_by c.toNat
decreasing_by exact Int.toNat_fdiv_two_lt (by assumption)

/-- Return the integer part of the square root of the input. -/
def isqrtRecursive (n : Int) : PyExcept Int := do
  if n < 0 then
    throw <| .valueError "isqrt() argument must be nonnegative"
  if n = 0 then
    return 0

  let c ← (n.bitLength - 1) // 2
  let a ← nsqrtRecursive n c

  return if n < a * a then a - 1 else a

end
