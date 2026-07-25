module

public import LimitDenominator.Definitions.Exceptions
public import LimitDenominator.Definitions.PythonPrimitives

/-!
Lean translation of the simplified integer form of the `limit_denominator` algorithm.

Here's the Python code that we'll translate. It is the listing from cpython#95723 with two
changes. The orientation variable `v` is removed: it is a derived quantity, equal to
`p*s - r*q` throughout, so the proofs recover it rather than carry it. And the precondition
`0 < n` is enforced rather than assumed, so that every input either gets an answer or an
exception, and none gets a wrong answer.

    def limit_denominator(m: int, n: int, l: int) -> tuple[int, int]:
        """
        Given a fraction m/n and a positive integer l, return integers r and s such
        that r/s is the closest fraction to m/n with denominator bounded by l.

        m/n need not be in lowest terms. Raises ValueError if l is less than one, or
        if n is not positive.

        On return, 0 < s <= l and gcd(r, s) = 1.
        """
        if l < 1:
            raise ValueError("max_denominator should be at least 1")
        if n <= 0:
            raise ValueError("denominator should be positive")

        a, b, p, q, r, s = n, m % n, 1, 0, m // n, 1
        while 0 < b and q + a // b * s <= l:
            a, b, p, q, r, s = b, a % b, r, s, p + a // b * r, q + a // b * s
        t, u = p + (l - q) // s * r, q + (l - q) // s * s
        return (r, s) if 2 * b * u <= n else (t, u)
-/

@[expose] public section

open scoped Python

/--
Closest fraction to `m / n` with denominator at most `l`, as a numerator/denominator pair.
-/
def limitDenominatorSimplified (m n l : Int) : PyExcept (Int × Int) := do
  if l < 1 then
    throw <| .valueError "max_denominator should be at least 1"
  if n ≤ 0 then
    throw <| .valueError "denominator should be positive"

  let mut (a, b, p, q, r, s) := (n, ← m % n, 1, 0, ← m // n, 1)
  -- Keep the right operand a `do` block, or the division is hoisted past the `0 < b` test.
  while ← pure (0 < b : Bool) <&&> (do return q + (← a // b) * s ≤ l) do
    (a, b, p, q, r, s) := (b, ← a % b, r, s, p + (← a // b) * r, q + (← a // b) * s)
  let (t, u) := (p + (← (l - q) // s) * r, q + (← (l - q) // s) * s)
  return if 2 * b * u ≤ n then (r, s) else (t, u)

end
