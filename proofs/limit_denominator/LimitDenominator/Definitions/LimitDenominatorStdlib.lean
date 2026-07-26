module

public import LimitDenominator.Definitions.Exceptions
public import LimitDenominator.Definitions.PythonPrimitives

/-!
Lean translation of the body of `Fraction.limit_denominator` as shipped in CPython's
`Lib/fractions.py`.

Here's the Python code that we'll translate, with the docstring and both explanatory comments
elided: the algorithm notes, and the note on the final comparison.

    def limit_denominator(self, max_denominator=1000000):
        if max_denominator < 1:
            raise ValueError("max_denominator should be at least 1")
        if self._denominator <= max_denominator:
            return Fraction(self)

        p0, q0, p1, q1 = 0, 1, 1, 0
        n, d = self._numerator, self._denominator
        while True:
            a = n//d
            q2 = q0+a*q1
            if q2 > max_denominator:
                break
            p0, q0, p1, q1 = p1, q1, p0+a*p1, q2
            n, d = d, n-a*d
        k = (max_denominator-q0)//q1

        if 2*d*(q0+k*q1) <= self._denominator:
            return Fraction._from_coprime_ints(p1, q1)
        else:
            return Fraction._from_coprime_ints(p0+k*p1, q0+k*q1)

Being a method, it needs two things stripped to become a function on integers. The attributes
`self._numerator` and `self._denominator` become parameters. And
`Fraction._from_coprime_ints`, which builds a `Fraction` from a pair it trusts to be in lowest
terms without checking, becomes the pair itself.

So the target's positive denominator and lowest-terms properties — which a `Fraction`
maintains, and which this listing therefore never tests — are not tested here either. They are
hypotheses of the correctness statement instead.

One name to watch: `n` here is the running numerator, where elsewhere in this project `n` is
the target's denominator. The shipped variable names are kept unchanged so that the Lean can
be read against the Python line for line.
-/

@[expose] public section

open scoped Python

/--
Closest fraction to `numerator / denominator` with denominator at most `maxDenominator`, as a
numerator/denominator pair.
-/
def limitDenominatorStdlib (numerator denominator maxDenominator : Int) :
    PyExcept (Int × Int) := do
  if maxDenominator < 1 then
    throw <| .valueError "max_denominator should be at least 1"
  if denominator ≤ maxDenominator then
    return (numerator, denominator)

  let mut (p0, q0, p1, q1) := (0, 1, 1, 0)
  let mut (n, d) := (numerator, denominator)
  repeat
    let a ← n // d
    let q2 := q0 + a * q1
    if q2 > maxDenominator then
      break
    (p0, q0, p1, q1) := (p1, q1, p0 + a * p1, q2)
    (n, d) := (d, n - a * d)
  let k ← (maxDenominator - q0) // q1

  if 2 * d * (q0 + k * q1) ≤ denominator then
    return (p1, q1)
  else
    return (p0 + k * p1, q0 + k * q1)

end
