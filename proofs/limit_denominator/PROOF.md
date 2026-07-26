# Why `limit_denominator` works

This is the prose companion to the Lean proof: the argument in ordinary mathematical
language, section by section, with pointers to where each step lives in the Lean source.
It follows the informal proof in [python/cpython#95723][issue], which is the original
source and is worth reading for its own account of the same argument.

[README.md](README.md) covers the code being proved correct, how to check the proof, and
what a reader has to trust. This file assumes you have read the algorithm listing there.

## Vocabulary

The proof uses a small fixed vocabulary, matching the names in the Lean source.

**Target** — the fraction `m / n` being approximated, as a pair of integers with `n`
strictly positive and `m` of either sign. Not necessarily in lowest terms.

**Denominator limit** — the strictly positive upper bound `l` on the denominator of the
result. (`max_denominator` is Python's parameter name; `l` is the concept.)

**Candidate** — a pair of integers `(y, z)` with `0 < z ≤ l`, standing for the fraction
`y / z`. Not required to be in lowest terms: the specification quantifies over all such
pairs, so the result must beat unreduced competitors too.

**At least as close** — the relation holding between two candidates when the first is no
further from the target than the second. Stated as an integer inequality, obtained from
`|m/n − r/s| ≤ |m/n − y/z|` by scaling by the positive quantity `n·s·z`:

```
|m·s − r·n|·z ≤ |m·z − y·n|·s
```

**Best approximation** — the candidate the algorithm must return: at least as close as
every other candidate, in lowest terms, with ties broken towards the smaller denominator,
and a tie that survives that towards the lower value. This is `isBestApproximation`.

**Loop candidate** — the candidate `(r, s)` held in the loop state, and still held on loop
exit. One of the two candidates the final comparison chooses between. (Not "lower bound":
which side of the target it lies on alternates, so that name would be right only half the
time.)

**Extended candidate** — the candidate `(t, u)` formed after loop exit by advancing the
*previous* loop candidate `(p, q)` as far towards the loop candidate as the denominator
limit allows: `t = p + k·r` and `u = q + k·s`, where `k = ⌊(l − q)/s⌋`.

**Orientation** — the value `±1` recording which side of the target the loop candidate
lies on. During the loop it is `p·s − r·q`; after the loop it is `t·s − r·u`, and the two
agree. It is a *derived* quantity, not state — see below.

**Bracket** — the property that the target lies between the loop candidate and the
extended candidate, inclusive on the loop candidate's side only. The heart of the proof:
every candidate strictly inside the bracket has denominator exceeding `l`.

**Residual** — an oriented scaled distance from the target to a candidate. The loop
candidate's is `b`, the extended candidate's is `c`; both are nonnegative because the
orientation is folded in.

**Simplified listing** — the three-argument integer function from
[the issue][issue], against which this argument is written. Lean:
`limitDenominatorSimplified`.

**Stdlib listing** — the body of `Fraction.limit_denominator` as shipped, which runs the same
calculation with a fast path in front of it. Lean: `limitDenominatorStdlib`.

## The specification

`isBestApproximation m n l r s` says that `r / s` is a best approximation to `m / n` with
denominator at most `l`. Written out
([`Specification.lean`](LimitDenominator/Definitions/Specification.lean)):

```lean
def isBestApproximation (m n l r s : Int) : Prop :=
  0 < s ∧ s ≤ l ∧ Int.gcd r s = 1 ∧
  ∀ y z : Int, 0 < z → z ≤ l →
    atLeastAsClose m n r s y z
    ∧ (atLeastAsClose m n y z r s → s ≤ z)
    ∧ (atLeastAsClose m n y z r s → s = z → r ≤ y)
```

All three of the quantified clauses are documented CPython promises: closest, then
smallest denominator, then smallest fraction. The second and third are conditioned on the
competitor being at least as close *in the other direction*, so together with the first
clause they only bite where the two distances are exactly equal.

Together the three clauses pin the answer down completely: if two pairs both satisfy
`isBestApproximation`, each is at least as close as the other, so the second clause equates
their denominators and the third then equates their numerators. That is
`isBestApproximation_unique`, in
[`BestApproximation.lean`](LimitDenominator/Proofs/BestApproximation.lean).

The behaviour for `n ≤ 0` is not left unspecified: the listing tests for it and raises a
`ValueError`, which is what lets `limitDenominatorSimplified_total` state that every input
either raises one of the two `ValueError`s or returns the best approximation. Python cannot
produce such a target, because a `Fraction`'s denominator is always positive, so that check
is a promise this project invents rather than one it records. The alternative is worse: every
line below assumes `0 < n`, so without the check a negative denominator returns a wrong
answer with no indication that anything went wrong.

## Removing the orientation from the state

The informal proof carries a seventh variable `v`, alternating between `1` and `−1`, and
states the first loop invariant as `(p·s − r·q)·v = 1`. Multiplying that through by `v`
gives `v = p·s − r·q`: the orientation is a function of the state. So it can be dropped
from the code, and the invariant clause becomes the plain disjunction

```
p·s − r·q = 1  or  p·s − r·q = −1
```

with no existential and no extra variable. That is why the Python listing in
[README.md](README.md) differs from the one in the issue by exactly this omission.

## Loop invariants

Before the loop and after every iteration, the state satisfies
([`LoopInvariant.lean`](LimitDenominator/Proofs/LoopInvariant.lean)):

| | |
| --- | --- |
| `det` | `p·s − r·q = ±1` |
| `numerator` | `a·r + b·p = m` |
| `denominator` | `a·s + b·q = n` |
| | `0 ≤ b < a` |
| | `0 ≤ q ≤ s ≤ l` |
| | `0 < s` |
| `p_eq_one_of_q_eq_zero` | `q = 0` implies `p = 1` |

The first six are the informal proof's six, and each holds by inspection initially and by
direct calculation across an iteration. The last one is discussed below; it is the one
clause that is not in the informal proof's list.

Note that at the end of an iteration, `s ≤ l` is exactly the condition under which the
loop was entered, namely `q + ⌊a/b⌋·s ≤ l`.

**Termination.** `b` is nonnegative and strictly decreases every iteration, since the new
`b` is `a mod b` with `0 < b`. In Lean this is the measure `b.toNat`, threaded by
[`forIn_loop_invariant`](LimitDenominator/Proofs/WhileLoop.lean).

**The residuals.** Two consequences of the invariants do the real work:

```
(p·n − m·q)·v = a        and        (m·s − r·n)·v = b
```

Both come from expanding `m` and `n` with `numerator` and `denominator`, then collapsing
with `det`. For instance

```
(p·n − m·q)·v = p(a·s + b·q)v − (a·r + b·p)qv = (p·s − r·q)·v·a = a
```

These are what make the absolute values in the specification disappear on the algorithm's
side: `|m·s − r·n| = b`, so the closeness relation against the returned pair reduces to
`b·z ≤ |m·z − y·n|·s`, with the only surviving absolute value on the competitor.

### Why the seventh invariant

The informal proof's tie-breaking argument reasons about the *history* of the loop: "an
examination of the while loop shows that the only time `q = 0` is before entry to the
while loop", and hence that the orientation is `+1` there. That is a statement about which
states are reachable, and it is not implied by the other six invariants — a state with
`q = 0`, `s = 1` and `p = −1` satisfies all six, and an algorithm reaching it would return
the *wrong* answer on a halfway tie, returning the upper bound instead of the lower one.

Formalising a reachability argument means putting it in the invariant, and the cheapest
form is `q = 0 → p = 1`: it holds initially by inspection, and after any iteration the new
`q` is the old `s`, which is positive, so the implication is vacuous. This is the only
place in the whole proof that needs to know the loop candidate is the *lower* of the two
bounds rather than the upper one.

## After the loop

Write `k = ⌊(l − q)/s⌋`, so that `t = p + k·r` and `u = q + k·s`, and define `c = a − k·b`.
Then, directly from the definitions and the loop invariants
([`AfterLoop.lean`](LimitDenominator/Proofs/AfterLoop.lean)):

```
t·s − r·u = p·s − r·q = v          (extending does not change the orientation)
c·r + b·t = m
c·s + b·u = n
(t·n − m·u)·v = c
```

From the definition of the floor, `k ≤ (l − q)/s < k + 1`; scaling by `s` gives
`q + k·s ≤ l < q + k·s + s`, that is

```
u ≤ l < u + s
```

and hence `0 < u`, since `u = 0` would give `l < s ≤ l`.

For `b ≤ c` and `0 < c`, split on how the loop exited. If `b = 0` then `c = a`, and
`0 < a` from `0 ≤ b < a`. Otherwise `0 < b` and `l < q + ⌊a/b⌋·s`, so
`⌊(l − q)/s⌋ < ⌊a/b⌋`, that is `k + 1 ≤ ⌊a/b⌋`; then `(k+1)·b ≤ ⌊a/b⌋·b ≤ a`, so
`b ≤ a − k·b = c`, and `0 < b ≤ c`.

Finally, `0 ≤ b = (m·s − r·n)·v` and `0 < c = (t·n − m·u)·v` say precisely that the target
lies between the two candidates: `r/s ≤ m/n < t/u` when `v = 1`, and `t/u < m/n ≤ r/s` when
`v = −1`.

### The degenerate tie

One further fact is needed, and it is the only one that draws on the seventh loop invariant:
if the two candidates share a denominator *and* are equidistant from the target, then the
orientation is `+1`. That is, `s = u` together with `b = c` implies `v = 1`.

The two hypotheses do different work. From `c = a − k·b`, the assumption `b = c` rearranges
to

```
a = (k+1)·b
```

which forces `k ≥ 1`: if `k ≤ 0` then `(k+1)·b ≤ b`, since `b ≥ 0`, so `a ≤ b`, contradicting
`b < a`. (It also forces `0 < b`, since `b = 0` would give `c = a` and hence `a = b = 0`,
against `0 < a`.)

The hypothesis `s = u` then does the rest. Written out it is `s = q + k·s`, and `k ≥ 1` with
`0 < s` gives `k·s ≥ s`, so `s ≥ q + s` and therefore `q ≤ 0`; with `q ≥ 0` from the
invariants,

```
q = 0
```

which is precisely what the seventh invariant needs. It gives `p = 1`, so the orientation
`p·s − r·q` is just `s` — and a positive unit is `1`.

The same equations pin down the rest of the configuration: `s = 1` from the orientation,
hence `u = 1` and `k = 1`, and then `s ≤ l < s + u` forces `l = 1`.

All of this is collected into the `Bracketing` structure, and nothing after that point
mentions the loop, its state, or `p` and `q`.

## The bracket

Any candidate `y / z` strictly between `r/s` and `t/u` has `z > l`. The identity is

```
z = z·(t·s − r·u)·v = (t·z − y·u)v·s + (y·s − r·z)v·u
```

Strictly inside the bracket, both `(t·z − y·u)v` and `(y·s − r·z)v` are positive — whichever
way round the two candidates lie, the orientation flips both signs together — so both are
at least `1`, and

```
z ≥ s + u > l
```

That is [`Bracketing.lt_of_inside`](LimitDenominator/Proofs/Bracket.lean). Contraposed, every
candidate within the denominator limit lies on one side or the other:
`(y·s − r·z)v ≤ 0` or `(t·z − y·u)v ≤ 0`.

### Candidates outside the bracket are no closer

Two pivot identities turn "on this side" into a distance bound. Writing
`F = (m·z − y·n)·v` for the candidate's oriented scaled distance:

```
b·z − F·s = n·(y·s − r·z)v
c·z + F·u = n·(t·z − y·u)v
```

On the loop candidate's side the right-hand side of the first is `≤ 0`, so `b·z ≤ F·s`,
and `F ≤ |m·z − y·n|` gives

```
b·z ≤ |m·z − y·n|·s
```

which is exactly `atLeastAsClose m n r s y z`. Symmetrically, on the extended candidate's
side the second identity gives `c·z ≤ |m·z − y·n|·u`.

Each pivot is an equality, so it says more than the bound: it says when the bound is
attained. If `b·z = |m·z − y·n|·s` then the first pivot's right-hand side vanishes, so
`(y·s − r·z)v = 0` and hence

```
y·s = r·z
```

that is, `y/z` equals the loop candidate as a *value* — though not necessarily as a pair,
since `(y, z)` need not be in lowest terms. Symmetrically, `c·z = |m·z − y·n|·u` forces
`t·z = y·u`. These are the **equality cases** of the two bounds
([`eq_of_loop_le` and `eq_of_extended_le`](LimitDenominator/Proofs/Bracket.lean)), and they
are what the tie-break clauses need: the first clause gives an inequality, and the equality
cases are what turn "no further away" into "the same fraction".

## Choosing between the two candidates

Comparing `|m/n − r/s|` with `|t/u − m/n|` and scaling by `n·s·u`, we compare
`|(m·s − r·n)u|` with `|(t·n − m·u)s|`; inserting a factor `v` does not change either
absolute value, and both `(m·s − r·n)v = b` and `(t·n − m·u)v = c` are nonnegative. So the
comparison is

```
b·u ≤ c·s
```

Adding `b·u` to both sides and using `c·s + b·u = n` makes this `2·b·u ≤ n`, which is what
the code computes ([`Bracketing.loop_nearer_iff`](LimitDenominator/Proofs/TieBreak.lean)).

On an exact tie, `b·u = c·s`, the code returns the loop candidate; its denominator really
is the smaller, since `c·s = b·u ≤ c·u` (as `0 < u` and `b ≤ c`) gives `s ≤ u` (as `0 < c`).

## Discharging the three clauses

Let `(R, S)` be whichever candidate is returned, and let `(y, z)` be any candidate. The
argument is in [`BestApproximation.lean`](LimitDenominator/Proofs/BestApproximation.lean).

**Positivity, the limit, lowest terms.** `0 < S ≤ l` is in `Bracketing`, and
`gcd(R, S) = 1` follows from `t·s − r·u = ±1`: any common divisor of `R` and `S` divides
that unit.

**Clause 1 — closest.** `(y, z)` lies on one side of the bracket or the other. On the
returned candidate's side, the bound is the one read off above. On the other side, the
bound is against the *other* candidate, and transfers because the returned one is the
nearer: from `c·z ≤ e·u` and `b·u ≤ c·s`, scaling and cancelling gives `b·z ≤ e·s`.

**Clause 2 — smaller denominator.** Now `(y, z)` is at least as close in both directions,
so the two distances are equal.

- If `(y, z)` is on the returned candidate's side, the equality case gives `y·S = R·z`. Since
  `gcd(R, S) = 1`, `S` divides `z`, and `0 < z` gives `S ≤ z`.
- If it is on the other side, then matching one candidate's distance exactly while lying
  beyond the other pins the comparison. When the loop candidate was returned, that forces an
  exact tie `b·u = c·s`, and then `(y, z)` matches the extended candidate's distance too; the
  equality case for the extended candidate gives `t·z = y·u`, so `u ≤ z`, and `s ≤ u` on a
  tie, so `s ≤ z`. When the extended candidate was returned the comparison was *strict*, and
  the same reasoning yields `b·u ≤ c·s`, a contradiction — so this case cannot arise.

**Clause 3 — lower value.** Additionally `S = z`.

- On the returned candidate's side, the equality case again gives `y·S = R·z`; with `S = z`
  that reads `y·S = R·S`, and `0 < S` gives `y = R`.
- On the other side, when the extended candidate was returned the case is impossible, as
  in clause 2. When the loop candidate was returned we are in the tie situation of clause
  2, with `u ≤ z = s ≤ u`, so `s = u = z`; then `b·u = c·s` gives `b = c`, so § "The
  degenerate tie" applies and the orientation is `+1`, giving `(t − r)·s = 1` and hence
  `t = r + 1`. And `t·z = y·u` with `z = u` gives `y = t = r + 1 > r`.

This is the only place the seventh invariant is used, and the only configuration in which
the two candidates share a denominator: `l = 1`, with a target exactly halfway between two
consecutive integers — for example `1/2`, where `0/1` and `1/1` are equally close and `0/1`
is returned.

## What the stdlib listing adds

Everything above is written for the simplified listing. The stdlib listing runs the same
calculation on the same state — permuted, and with its unconditional first iteration doing
the simplified listing's initialisation — so the invariants, the bracket and the tie-breaking
carry over unchanged. Two of its differences are mathematical rather than mechanical, and
both trade on its target being in lowest terms.

**The fast path.** When the target's denominator is already within the limit, the shipped
code returns the target itself and never reaches the loop. That answer is a best
approximation for a reason the argument above does not supply. Its distance to the target is
zero, so it is at least as close as every candidate, which is clause 1. And a candidate
`y / z` also at distance zero satisfies `y·n = m·z`, so `n` divides `z` — the target being in
lowest terms — giving `n ≤ z` for clause 2; if moreover `z = n` then `y = m`, which settles
clause 3. This is
[`isBestApproximation_self`](LimitDenominator/Proofs/BestApproximation.lean).

**No `0 < b` test.** The shipped loop condition tests only `q2 > max_denominator`, leaving
its division by `b` unguarded. It needs no guard: past the fast path the target is in lowest
terms with `l < n`, and then `b` is never zero. Were it zero, the two invariants recovering
the target would read `a·r = m` and `a·s = n`, making `a` a common divisor of `m` and `n` and
so `a = 1`, whence `n = s ≤ l` — the fast path would have taken it. This is
[`LoopInvariant.b_pos`](LimitDenominator/Proofs/LoopInvariant.lean), and it is the argument
of the issue's § "Optimization".

## What the informal proof needs that this one does not

The informal proof establishes `2·b·q < n` at every point of the calculation and uses it in
its tie-breaking argument, to force `q < u` and hence `q = 0`. The route above reaches the
same place through the equality analysis of clause 2 instead — `u ≤ z` and `s ≤ u` squeeze
`s = u`, and `b = c` follows — so `2·b·q < n` never appears in the Lean proof.

[issue]: https://github.com/python/cpython/issues/95723
