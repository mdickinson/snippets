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
every other candidate, with ties broken towards the smaller denominator, and a tie that
survives that towards the lower value. This is `isBestApproximation`. Being in lowest terms
is not part of it, but follows from it.

**Loop candidate** — the candidate `(r, s)` held in the loop state, and still held on loop
exit. One of the two candidates the final comparison chooses between. (Not "lower bound":
which side of the target it lies on alternates, so that name would be right only half the
time.)

**Extended candidate** — the candidate `(t, u)` formed after loop exit by advancing the
*previous* loop candidate `(p, q)` as far towards the loop candidate as the denominator
limit allows: `t = p + k·r` and `u = q + k·s`, where `k = ⌊(l − q)/s⌋`.

**Orientation** — the value `±1` recording which side of the target the loop candidate
lies on, written `v`. During the loop it is `p·s − r·q`; after the loop it is `t·s − r·u`,
and the two agree. It is a *derived* quantity, not state — see below.

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
  0 < s ∧ s ≤ l ∧
  ∀ y z : Int, 0 < z → z ≤ l →
    atLeastAsClose m n r s y z
    ∧ (atLeastAsClose m n y z r s → s ≤ z)
    ∧ (atLeastAsClose m n y z r s → s = z → r ≤ y)
```

All three of the quantified clauses are CPython promises, though not all documented ones:
*closest* is the docstring's, while *smaller denominator* and *the lower value* come from the
algorithm-notes comment in the source. The second and third are conditioned on the competitor
being at least as close *in the other direction*, so together with the first clause they only
bite where the two distances are exactly equal.

Together the three clauses pin the answer down completely: if two pairs both satisfy
`isBestApproximation`, each is at least as close as the other, so the second clause equates
their denominators and the third then equates their numerators. That is
`isBestApproximation_unique`, in
[`BestApproximation.lean`](LimitDenominator/Proofs/BestApproximation.lean). Note that this
quantifies over all pairs with a positive denominator within the limit, reduced or not.

Lowest terms is a *consequence* of these clauses, not one of them. If `r` and `s` shared a
factor `g > 1`, the reduced pair `(r/g, s/g)` would be a candidate too — positive
denominator, strictly smaller, so still within the limit — and exactly as close, since
scaling a pair down by `g` scales its residual `m·s − r·n` down by `g`, which cancels
against the `s` on the other side of the closeness relation. The second clause applied to it
would give `s ≤ s/g`, which is false. So the specification pins down the representation and
not merely the value, and CPython's `gcd(r, s) = 1` is earned rather than asked for. That is
`isBestApproximation.gcd_eq_one`, in the same file.

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

with no existential and no extra variable. That is one of the two ways the Python listing in
[README.md](README.md) differs from the one in the issue; the other is that the issue's two
stated preconditions, `0 < l` and `0 < n`, are enforced there rather than assumed.

The *proof* names it again once the loop is over. `Bracketing` (§ "After the loop") takes `v`
as a parameter and records the informal proof's equation verbatim:

```
(t·s − r·u)·v = 1
```

Over the integers that single equation says both that `v` is a unit and that it agrees with
the determinant, and between them those are everything the orientation is ever asked for:

- it collapses the two bracket identities, where `v` meets its own determinant;
- it makes `v` nonzero, which is all that cancelling `v` out of an inequality takes.

Nothing below ever needs `v = ±1` on its own, so the proof never derives it. What naming `v`
buys is legibility: the statements of § "The bracket" would otherwise spell the orientation
out as `t·s − r·u` throughout, which also drags `t` and `u` into statements that do not
depend on them.

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
c·r + b·t = m                      (not formalised; shown for symmetry with the next)
c·s + b·u = n
(t·n − m·u)·v = c
```

From the definition of the floor, `k ≤ (l − q)/s < k + 1`; scaling by `s` gives
`q + k·s ≤ l < q + k·s + s`, that is

```
u ≤ l < u + s
```

and hence `0 < u`: it is nonnegative, since `q ≥ 0` and `k ≥ 0` — the latter because
`q ≤ s ≤ l` makes `l − q` nonnegative — and `u = 0` would give `l < s ≤ l`.

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

which is precisely what the seventh invariant needs: it gives `p = 1`. And with `q` gone,
`s = u` reads `s = k·s`, which for positive `s` leaves no room for a second step, so `k = 1`
and

```
t = p + k·r = r + 1
```

The two candidates are consecutive integers, in that order. That is the form the fact is
recorded in, as `Bracketing`'s `t_eq_of_tie`, because it is the form the third clause uses;
the orientation does not appear in it at all. The same equations pin down the rest of the
configuration — `s = 1` from the orientation, hence `u = 1`, and then `s ≤ l < s + u` forces
`l = 1` — but nothing needs those, so they are not derived.

All of this is collected into the `Bracketing` structure, and nothing after that point
mentions the loop, its state, or `p` and `q`.

## The bracket

Two identities split a candidate's numerator and denominator along the same pair of
cross-products. Multiplying out either right-hand side leaves the left-hand side times
`(t·s − r·u)·v`, which is `1`:

```
y = (t·z − y·u)v·r + (y·s − r·z)v·t
z = (t·z − y·u)v·s + (y·s − r·z)v·u
```

The second closes the bracket. A candidate `y / z` strictly between `r/s` and `t/u` has both
`(t·z − y·u)v` and `(y·s − r·z)v` positive — whichever way round the two candidates lie, the
orientation flips both signs together — so both are at least `1`, and

```
z ≥ s + u > l
```

That is [`Bracketing.lt_of_inside`](LimitDenominator/Proofs/Bracket.lean). Read the other
way, the same identity says a candidate with `z > 0` has at least one cross-product positive,
since two nonpositive ones would make `z` nonpositive. Together, every candidate the
specification quantifies over lies strictly beyond *exactly one* of the two candidates:

```
(y·s − r·z)v ≤ 0 < (t·z − y·u)v      or      (t·z − y·u)v ≤ 0 < (y·s − r·z)v
```

That is `Bracketing.cases`, and it is the only case split in the rest of the argument. The
first alternative is the loop candidate's side of the bracket, the second the extended
candidate's.

Both identities do further work in the tie-break clauses below. There one cross-product
*vanishes* rather than being positive, and the denominator identity is left exhibiting `z` as
a positive multiple of a single one of the two denominators — which is how a rival is shown
to need at least that candidate's denominator, with no appeal to divisibility. If its
denominator matches exactly, the surviving cross-product is forced to `1`, and the numerator
identity then reads the rival's numerator straight off.

### Candidates outside the bracket are no closer

Two pivot identities turn "on this side" into a distance bound. Writing
`F = (m·z − y·n)·v` for the candidate's oriented scaled distance:

```
b·z − F·s = n·(y·s − r·z)v
c·z + F·u = n·(t·z − y·u)v
```

Neither pivot needs the determinant: each is a ring identity in an arbitrary `v`, given only
the residual that defines `b` or `c`.

On the loop candidate's side the right-hand side of the first is `≤ 0`, so `b·z ≤ F·s`, and
`b ≥ 0` makes that a chain with a nonnegative lower end. Unfolding the two abbreviations,

```
0 ≤ (m·s − r·n)v·z ≤ (m·z − y·n)v·s
```

and this is where the specification's absolute values are reached — at the end of the chain,
and in one step. Taking absolute values of the two ends puts a factor of `|v|` on each side:
the lower end is nonnegative, so it *equals* its absolute value `|m·s − r·n|·z·|v|`, and the
upper end is at most `|m·z − y·n|·s·|v|`. Cancelling the positive `|v|` leaves

```
|m·s − r·n|·z ≤ |m·z − y·n|·s
```

which is exactly `atLeastAsClose m n r s y z`. This is the only thing the orientation is
needed for anywhere in the proof, and it takes only `v ≠ 0`: nothing here asks whether `v` is
`1` or `−1`, and nothing has to rewrite `|m·s − r·n|` to `b`. The cancellation is
`Int.abs_cancel` in [`SupportLemmas.lean`](LimitDenominator/Proofs/SupportLemmas.lean).

Symmetrically, the second identity gives `|m·u − t·n|·z ≤ |m·z − y·n|·u` on the extended
candidate's side, cancelling the orientation `−v` — the one that makes *that* candidate's
residual nonnegative.

The chain says more than the bound: it says when the bound is attained. A candidate whose
absolute-value bound is an equality had the oriented inequality as an equality already,
because the chain is then squeezed between two equal ends. The first pivot's right-hand side
therefore vanishes, giving

```
(y·s − r·z)v = 0
```

and symmetrically `(t·z − y·u)v = 0` on the other side. These are the **equality cases** of
the two bounds, and each is returned by the same lemma that gives its bound
([`Bracket.lean`](LimitDenominator/Proofs/Bracket.lean)), the two sharing a chain. They are
what the tie-break clauses need: the first clause gives an inequality, and the equality cases
turn "no further away" into a vanishing cross-product. Since `v` is nonzero, a vanishing
cross-product says `y·s = r·z` — that `y/z` equals the loop candidate as a *value*, though
not necessarily as a pair, since `(y, z)` need not be in lowest terms. The proof never takes
that step, using the vanishing directly in the two identities instead.

## Choosing between the two candidates

Comparing `|m/n − r/s|` with `|t/u − m/n|` and scaling by `n·s·u`, we compare
`|(m·s − r·n)u|` with `|(t·n − m·u)s|`; inserting a factor `v` does not change either
absolute value, and both `(m·s − r·n)v = b` and `(t·n − m·u)v = c` are nonnegative. So the
comparison is

```
b·u ≤ c·s
```

That reading of `b·u ≤ c·s` is why the code's test is the right test, but it is motivation
rather than a step: the proof reaches the specification's absolute values through the pivots
of the previous section, and never through this paragraph's appeal to `|v| = 1`. What it does
formalise is the arithmetic below.

Adding `b·u` to both sides and using `c·s + b·u = n` makes this `2·b·u ≤ n`, which is what
the code computes ([`Bracketing.loop_nearer_iff`](LimitDenominator/Proofs/TieBreak.lean)).

On an exact tie, `b·u = c·s`, the code returns the loop candidate; its denominator really
is the smaller, since `c·s = b·u ≤ c·u` (as `0 < u` and `b ≤ c`) gives `s ≤ u` (as `0 < c`).

## Discharging the three clauses

Let `(y, z)` be any candidate. The argument is in
[`BestApproximation.lean`](LimitDenominator/Proofs/BestApproximation.lean). It splits once,
on `Bracketing.cases`, and then reads all three clauses off on each side; with the two
choices of returned candidate that is four subcases, each a short chain of the pieces above.

**Positivity and the limit.** `0 < S ≤ l` is in `Bracketing`, for either candidate.

Coprimality of `R` and `S` plays no part in this section at all. It is not a clause to
discharge — it follows from the specification, as § "The specification" describes — and the
denominator comparisons below do not need it either: they run on the *determinant*, which is
what coprimality would itself have followed from. So nothing here reasons about divisibility.

**The loop candidate is returned**, the comparison being `b·u ≤ c·s`.

- *On the loop candidate's side*, the bound of § "Candidates outside the bracket" is clause 1
  as it stands. A rival matching it has `(y·s − r·z)v = 0`, so the denominator identity
  collapses to `z = (t·z − y·u)v·s` with a positive cofactor, giving `s ≤ z` — clause 2. If
  moreover `s = z`, that cofactor is `1`, and the numerator identity gives `y = r` — clause
  3.
- *On the extended candidate's side*, clause 1 needs the comparison. The extended pivot
  scaled by `s`, and `b·u ≤ c·s` scaled by `z`, chain into `0 ≤ (m·s − r·n)v·(u·z) ≤ −(m·z −
  y·n)v·(u·s)`; cancelling `|v|` and then the common `u` gives the bound. A rival matching it
  makes both steps of that chain equalities, so the comparison is an exact tie `b·u = c·s`
  *and* `(t·z − y·u)v = 0`. The vanishing gives `u ≤ z`, the tie gives `s ≤ u` (§ "Choosing
  between the two candidates"), so `s ≤ z` — clause 2. If `s = z`, those squeeze `s = u = z`,
  whence `b = c`; § "The degenerate tie" then gives `t = r + 1`, while the numerator identity
  gives `y = t`. So `y = r + 1 > r` — clause 3.

**The extended candidate is returned**, the comparison being strict, `c·s < b·u`.

- *On the extended candidate's side*, the bound is read off directly, and its equality case
  gives `(t·z − y·u)v = 0`, hence `u ≤ z` and, when `u = z`, `y = t`.
- *On the loop candidate's side*, the loop pivot scaled by `u` and the strict comparison
  scaled by `z` give a *strict* bound, `|m·u − t·n|·z < |m·z − y·n|·u`. Clause 1 follows, and
  both tie-break clauses are vacuous: no rival on that side can be at least as close in both
  directions.

The seventh invariant is used in exactly one of those four subcases, and only for the one
configuration in which the two candidates share a denominator: `l = 1`, with a target exactly
halfway between two consecutive integers — for example `1/2`, where `0/1` and `1/1` are
equally close and `0/1` is returned.

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
the target would read `a·r = m` and `a·s = n`, making `a` a common divisor of `m` and `n`, so
`a = ±1`; and `0 ≤ b < a` forces `a` positive, so `a = 1`, whence `n = s ≤ l` — the fast path
would have taken it. This is
[`LoopInvariant.b_pos`](LimitDenominator/Proofs/LoopInvariant.lean), and it is the argument
of the issue's § "Optimization".

## What the informal proof needs that this one does not

The informal proof establishes `2·b·q < n` at every point of the calculation and uses it in
its tie-breaking argument, to force `q < u` and hence `q = 0`. The route above reaches the
same place through the equality analysis of clause 2 instead — `u ≤ z` and `s ≤ u` squeeze
`s = u`, and `b = c` follows — so `2·b·q < n` never appears in the Lean proof.

[issue]: https://github.com/python/cpython/issues/95723
