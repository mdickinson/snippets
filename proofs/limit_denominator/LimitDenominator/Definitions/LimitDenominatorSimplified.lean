module

public import LimitDenominator.Definitions.Exceptions
public import LimitDenominator.Definitions.PythonPrimitives

/-!
Lean translation of the simplified integer form of the `limit_denominator` algorithm.

Here's the Python code that we'll translate. It is the listing from cpython#95723 with the
orientation variable `v` removed: `v` is a derived quantity, equal to `p*s - r*q`
throughout, so the proofs recover it rather than carry it.

    def limit_denominator(m: int, n: int, l: int) -> tuple[int, int]:
        """
        Given a fraction m/n and a positive integer l, return integers r and s such
        that r/s is the closest fraction to m/n with denominator bounded by l.

        m/n need not be in lowest terms, but n must be positive.

        On return, 0 < s <= l and gcd(r, s) = 1.
        """
        if l < 1:
            raise ValueError("max_denominator should be at least 1")

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

  let mut (a, b, p, q, r, s) := (n, ← m % n, 1, 0, ← m // n, 1)
  while ← pyAnd (0 < b) (do return q + (← a // b) * s ≤ l) do
    (a, b, p, q, r, s) := (b, ← a % b, r, s, p + (← a // b) * r, q + (← a // b) * s)
  let (t, u) := (p + (← (l - q) // s) * r, q + (← (l - q) // s) * s)
  return if 2 * b * u ≤ n then (r, s) else (t, u)

end
