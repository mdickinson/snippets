# limit_denominator correctness proof

A Lean 4 formalisation of the correctness of the algorithm behind Python's
`Fraction.limit_denominator`, following the informal proof in
[python/cpython#95723](https://github.com/python/cpython/issues/95723).

This file is a glossary: it fixes the vocabulary used in the Lean source, the README and
in discussion of the proof. It is working scaffolding for the planning and implementation
phases, and is expected to be folded away once the project settles.

## Language

### The problem

**Target**:
The fraction `m / n` being approximated. Always written as a pair of integers `m` (any
sign) and `n` (strictly positive), not necessarily in lowest terms.
_Avoid_: input, x, self

**Denominator limit**:
The upper bound `l` on the denominator of the result. Strictly positive.
_Avoid_: max_denominator (that is Python's parameter name, not the concept), bound, limit,
maximum

**Candidate**:
A pair of integers `(y, z)` with `0 < z ≤ l`, standing for the fraction `y / z`. Not
required to be in lowest terms — the specification quantifies over all such pairs.
_Avoid_: approximation, fraction

**At least as close**:
The relation holding between two candidates when the first is no further from the target
than the second. Stated as an integer inequality obtained by scaling
`|m/n - r/s| ≤ |m/n - y/z|` by the positive quantity `n * s * z`.
_Avoid_: closer, nearer, better

**Valid target**:
The targets a given implementation is required to handle, supplied as a parameter to the
correctness statement. The simplified listing's valid targets are all `m / n` with
`0 < n`; the stdlib listing's are additionally required to be in lowest terms, which
CPython guarantees because `self` is a normalised `Fraction`.
_Avoid_: precondition, domain, admissible input

**Best approximation**:
The candidate that the algorithm is required to return: closest to the target, with ties
broken towards the smaller denominator and any remaining tie towards the smaller
fraction. In lowest terms.
_Avoid_: best rational approximation, convergent, semiconvergent, best upper/lower
approximation — the proof deliberately avoids continued fraction theory and none of that
vocabulary is needed.

### The algorithm

**Loop candidate**:
The candidate `(r, s)` held in the loop state, and still held on loop exit. One of the two
candidates the final comparison chooses between.
_Avoid_: lower bound, upper bound — which side of the target it lies on depends on the
orientation, so those names are only correct half the time.

**Extended candidate**:
The candidate `(t, u)` formed after loop exit by advancing the previous loop candidate
`(p, q)` as far towards the loop candidate as the denominator limit allows:
`t = p + k * r` and `u = q + k * s`, where `k = (l - q) / s`.
_Avoid_: second candidate, other bound, mediant

**Orientation**:
The value `v`, always `1` or `-1`, recording which side of the target the loop candidate
lies on: `r/s ≤ m/n < t/u` when `v = 1`, and `t/u < m/n ≤ r/s` when `v = -1`. A proof-only
notion — it is existentially quantified in the loop invariant and appears nowhere in the
Lean translations, since the returned value does not depend on it.
_Avoid_: sign, parity, direction

**Bracket**:
The property that the target lies between the loop candidate and the extended candidate,
inclusive on the loop candidate's side only. The heart of the proof: every candidate
strictly inside the bracket has denominator exceeding `l`.
_Avoid_: straddle, enclose, interval

### The two listings

**Simplified listing**:
The three-argument integer function given in cpython#95723, against which the informal
proof is written. Takes and returns plain integers, has no fast path, tests the loop
condition at the top of the loop, and carries the orientation. Lean:
`limitDenominatorSimplified`.
_Avoid_: reference listing, toy version, model

**Stdlib listing**:
The body of `Fraction.limit_denominator` as it appears in CPython's `Lib/fractions.py`.
Operates on an already-reduced fraction, has a fast path for denominators already within
the limit, and breaks out of a `while True` loop from the middle. Lean:
`limitDenominatorStdlib`.
_Avoid_: shipped listing, real version, production version, actual code
