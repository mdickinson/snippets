/-
Lean translation of the recursive form of the CPython `isqrt` algorithm.

Here's the algorithm expressed recursively in Python. The core function `nsqrt`
recursively computes a (positive) "near square root" of a positive integer `n`; the
outer `isqrt` function deals with negative and zero inputs and for positive `n` applies
the final correction to the near square root (if necessary) to turn it into the integer
square root.

    def nsqrt(n: int, c: int) -> int:
        """Recursively compute a near square root of a positive integer n."""
        if c == 0:
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

There's a barrier to a direct translation of the above code. By default Lean requires
functions to be total, and our Python `nsqrt` isn't: for negative `c` it recurses forever
(the counter `c // 2` never reaches `0`). Two adjustments make the Lean version total
without changing its behaviour on the inputs that actually occur — `isqrt` only ever calls
`nsqrt` with `c ≥ 0`:

- The base case tests `c <= 0` rather than `c == 0`, so a negative `c` returns `1`
  immediately instead of recursing.
- Lean recurses on the measure `c.toNat` (`termination_by`). For `c > 0` the counter
  satisfies `0 ≤ c // 2 < c`, so the measure strictly decreases and Lean accepts the
  definition; for `c ≤ 0` the base case applies, so the measure never has to decrease.
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

/-- Floor-halving strictly decreases the `ℕ`-measure `·.toNat`: `⌊c/2⌋.toNat < c.toNat`
for `0 < c` (since `0 ≤ ⌊c/2⌋ < c`). This is what makes `nsqrtRecursive`'s recursion on
`c.toNat` well-founded; its `decreasing_by` — and the matching one in the correctness
proof — discharge with it. -/
theorem Int.toNat_fdiv_two_lt {c : Int} (hc : 0 < c) : (Int.fdiv c 2).toNat < c.toNat := by
  have : Int.fdiv c 2 < c := by
    rw [Int.fdiv_eq_ediv_of_nonneg c (by omega), Int.ediv_lt_iff_lt_mul (by omega)]; omega
  have : 0 ≤ Int.fdiv c 2 := Int.fdiv_nonneg (by omega) (by omega)
  omega

/-- Return a near square root of a positive integer n. -/
def nsqrtRecursive (n c : Int) : PyExcept Int := do
  if c <= 0 then
    return 1
  else
    let k ← (c - 1) // 2
    -- The counter `c` halves each step; written as the pure `Int.fdiv c 2` (not `← c // 2`)
    -- because it is the recursion's decreasing measure and Lean must see its value to prove
    -- termination. Division by the literal 2 can never raise, so this loses no behaviour.
    let a ← nsqrtRecursive (← n >> 2 * k + 2) (Int.fdiv c 2)
    return (← a << k) + (← (← n >> k + 2) // a)
termination_by c.toNat
decreasing_by exact Int.toNat_fdiv_two_lt (by omega)

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
