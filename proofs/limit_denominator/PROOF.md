# Why `limit_denominator` works

This is the prose companion to the Lean proof: the argument in ordinary mathematical
language, section by section, with pointers to where each step lives in the Lean source.
It follows the informal proof in [python/cpython#95723][issue], which is the original
source and is worth reading for its own account of the same argument.

[README.md](README.md) covers the code being proved correct, how to check the proof, and
what a reader has to trust. This file assumes you have read the algorithm listing there.

The mathematics lives in one file,
[`Experiment.lean`](LimitDenominator/Proofs/Experiment.lean), and the pointers below
name its theorems. The two correctness files are mechanics, connecting each listing to
that file's algorithm; § "From the listing to the algorithm" covers them, and § "The two
listings agree" the one theorem stated about both.

## Vocabulary

The proof uses a small fixed vocabulary, matching the names in the Lean source.

**Target** — the fraction `m / n` being approximated, as a pair of integers with `n`
strictly positive and `m` of either sign. Not necessarily in lowest terms.

**Denominator limit** — the strictly positive upper bound `l` on the denominator of the
result. (`max_denominator` is Python's parameter name; `l` is the concept.) In Lean the
target and the limit travel together as an `Arguments`, a structure whose fields are
`m`, `n` and `limit` together with proofs of `0 < n` and `1 ≤ limit`.

**Candidate** — a pair of integers `(y, z)` with `0 < z ≤ l`, standing for the fraction
`y / z`. Not required to be in lowest terms: the specification quantifies over all such
pairs, so the result must beat unreduced competitors too. Lean: `Candidate`, again a
structure carrying its two bounds as proof fields.

**Distance** — from the target to a candidate, scaled by both denominators:
`|y·n − m·z|` for `y / z`, which is `|y/z − m/n|` times the positive quantity `n·z`.
Lean: `dist`.

**At least as close** — the relation holding between two candidates when the first is no
further from the target than the second. Stated as an integer inequality, obtained from
`|r/s − m/n| ≤ |y/z − m/n|` by scaling by the positive quantity `n·s·z`:

```
|r·n − m·s|·z ≤ |y·n − m·z|·s
```

That is `atLeastAsClose` in the specification, and `dist rs · z ≤ dist yz · s` in the
proof's terms.

**Better** — the proof's ordering on candidates: `r / s` is better than `y / z` if it is
strictly closer, or equally close with `s ≤ z`. Despite the name it is reflexive, and it
is transitive. Lean: `better`.

**Best approximation** — a candidate better than every candidate. Lean: `best`; in the
specification's vocabulary, `isBestApproximation`, and the two agree (§ "The
specification"). Being in lowest terms is not part of it, but follows from it.

**Ambiguous** — the one situation in which two candidates are best: the limit is `1` and
the target is a half-integer, `w + 1/2` for some integer `w`. Lean: `ambiguous` in the
proof, `isAmbiguous` in the specification, the same formula written twice.

**Loop candidate** — the candidate `(r, s)` held in the loop state, and still held on
loop exit. One of the two candidates the final comparison chooses between. (Not "lower
bound": which side of the target it lies on alternates, so that name would be right only
half the time.) Lean: `rs`, once the loop is over.

**Extended candidate** — the candidate `(t, u)` formed after loop exit by advancing the
*previous* loop candidate `(p, q)` as far towards the loop candidate as the denominator
limit allows: `t = p + k·r` and `u = q + k·s`, where `k = ⌊(l − q)/s⌋`. Lean: `tu`.

**Orientation** — the value `±1` recording which side of the target the loop candidate
lies on, written `v`. Carried in the loop state, as the listing carries it, and tied to
the rest of the state by the invariant `(p·s − r·q)·v = 1` — see below.

**Bracket** — the property that the target lies between the loop candidate and the
extended candidate, inclusive on the loop candidate's side only. The heart of the proof:
every candidate strictly inside the bracket has denominator exceeding `l`.

**Residual** — an oriented scaled distance from the target to a candidate. The loop
candidate's is `b`, the extended candidate's is `c`; both are nonnegative because the
orientation is folded in.

**Simplified listing** — the three-argument integer function from [the issue][issue],
against which this argument is written. Lean: `limitDenominatorSimplified`.

**Stdlib listing** — the body of `Fraction.limit_denominator` as shipped, which runs the
same calculation with a fast path in front of it. Lean: `limitDenominatorStdlib`.

## The specification

`isBestApproximation m n l r s` says that `r / s` is a best approximation to `m / n`
with denominator at most `l`. Written out
([`Specification.lean`](LimitDenominator/Definitions/Specification.lean)):

```lean
def isBestApproximation (m n l r s : Int) : Prop :=
  0 < s ∧ s ≤ l ∧
  ∀ y z : Int, 0 < z → z ≤ l →
    atLeastAsClose m n r s y z
    ∧ (atLeastAsClose m n y z r s → s ≤ z)
```

Both quantified clauses are CPython promises, though not both documented ones: *closest*
is the docstring's, while *smaller denominator* comes from the algorithm-notes comment
in the source. The second is conditioned on the competitor being at least as close *in
the other direction*, so together with the first clause it only bites where the two
distances are exactly equal.

**What the two clauses determine.** Two candidates can satisfy both clauses at once only
by being equidistant from the target with the same denominator, and that is possible
only in the ambiguous case, where `⌊m/n⌋ / 1` and `(⌊m/n⌋ + 1) / 1` are both best. Two
theorems say so, in the closing section of
[`Experiment.lean`](LimitDenominator/Proofs/Experiment.lean):
`isBestApproximation_unique_of_not_ambiguous`, that outside the ambiguous case at most
one pair satisfies the specification, and `isBestApproximation_iff_of_ambiguous`, that
inside it exactly those two pairs do. Both quantify over all pairs with a positive
denominator within the limit, reduced or not. Neither is read off the clauses; both come
through the algorithm, whose bracket is what says where the best candidates are (§ "What
the specification determines").

CPython's promise of the floor in the ambiguous case is not part of the specification,
which says what "best" means and nothing about how an implementation chooses between two
equally good answers. It is a statement about each listing instead,
`limitDenominatorSimplified_returns_floor_of_ambiguous` and
`limitDenominatorStdlib_returns_floor_of_ambiguous`.

**Lowest terms** is a *consequence* of the two clauses, not one of them. If `r` and `s`
shared a factor `g > 1`, the reduced pair `(r/g, s/g)` would be a candidate too —
positive denominator, strictly smaller, so still within the limit — and exactly as
close, since scaling a pair down by `g` scales its residual `r·n − m·s` down by `g`,
which cancels against the `s` on the other side of the closeness relation. The second
clause applied to it would give `s ≤ s/g`, which is false. So the specification pins
down the representation and not merely the value, and CPython's `gcd(r, s) = 1` is
earned rather than asked for. That is `isBestApproximation.gcd_eq_one`. The Lean proof
does not run that argument: it goes through the algorithm too, a best approximation
being one of the two bracket endpoints and the bracket's determinant a Bézout identity
for each (§ "What the specification determines").

**The bridge.** Everything the proof establishes is stated in its own vocabulary, of
`Arguments`, `Candidate`, `dist`, `better` and `best`, and meets the specification's in
that one closing section. `best_iff_isBestApproximation` says `best` and
`isBestApproximation` agree on any candidate: `better`'s two arms are the two clauses.
Forwards, either arm gives the closeness clause, and once the rival is at least as close
the strict arm is impossible, so the tie arm supplies the denominator comparison.
Backwards, a strict inequality is the first arm and an equality feeds the second clause,
which gives the second arm. Both directions are unfoldings, finished by `omega`.
`ambiguous_iff_isAmbiguous` is the two formulas being one, `Iff.rfl`. Each statement
about the specification builds an `Arguments` from `0 < n` and `1 ≤ l`, the latter from
`0 < s ≤ l` or from `l = 1`, translates its hypotheses across the bridge, applies the
proof's result, and translates back.

The behaviour for `n ≤ 0` is not left unspecified: the listing tests for it and raises a
`ValueError`, which is what lets `limitDenominatorSimplified_total` state that every
input either raises one of the two `ValueError`s or returns the best approximation.
Python cannot produce such a target, because a `Fraction`'s denominator is always
positive, so that check is a promise this project invents rather than one it records.
The alternative is worse: every line below assumes `0 < n`, so without the check a
negative denominator returns a wrong answer with no indication that anything went wrong.
The three statements about the specification carry `0 < n` as a hypothesis for the same
reason: each needs an `Arguments` to hand the proof, and there is none without it.

## The orientation in the state

The informal proof carries a seventh variable `v`, alternating between `1` and `−1`, and
states the first loop invariant as `(p·s − r·q)·v = 1`. Multiplying that through by `v`
gives `v = p·s − r·q`: the orientation is a function of the rest of the state, so the
invariant clause could equally be written as the plain disjunction

```
p·s − r·q = 1  or  p·s − r·q = −1
```

with no extra variable. Nothing is lost either way, and the listing in
[README.md](README.md) carries `v` as the issue's does, which leaves the two enforced
preconditions as the only way the two listings differ.

The Lean state carries it too, and records the informal proof's equation verbatim as the
invariant `det`; after the loop it is `bracket_det`,

```
(t·s − r·u)·v = 1
```

extending having changed neither the determinant nor the orientation. Over the integers
that single equation says both that `v` is a unit and that it agrees with the
determinant. `v_cases` reads `v = 1` or `v = −1` off it, and `v_nonzero` follows.

What naming `v` buys is that the two sides of the bracket are handled by one statement
each. The proof's order relation `lev` is orientation-aware: `st.lev ef gh` is the
integer inequality `e·h·v ≤ g·f·v`, which says `e/f ≤ g/h` when `v = 1` and `g/h ≤ e/f`
when `v = −1`; `eqv` is the corresponding equality, and since `v` is nonzero it is
equality of fractions whichever way the bracket points. In those terms the bracket reads
`r/s ≤ m/n ≤ t/u` in either orientation, and each statement about "the loop candidate's
side" is made once rather than once per sign.

## Loop invariants

Before the loop and after every iteration, the state satisfies the following; each is a
field of the `LoopState` structure, beside the seven numbers themselves, so that a value
of that type is a state together with the proof that it is a valid one:

| Field | Invariant |
| --- | --- |
| `det` | `(p·s − r·q)·v = 1` |
| `a_eq_pq_cross` | `(p·n − m·q)·v = a` |
| `b_eq_rs_cross` | `(m·s − r·n)·v = b` |
| `b_nonneg`, `b_lt_a` | `0 ≤ b < a` |
| `q_nonneg` | `0 ≤ q` |
| `s_pos`, `s_le_limit` | `0 < s ≤ l` |
| `v_eq_one_of_q_eq_zero` | `q = 0` implies `v = 1` |

`det` and the four inequalities are the informal proof's. In place of its two identities
recovering the target, `a·r + b·p = m` and `a·s + b·q = n`, the state carries the two
residual identities: `a` and `b` are the cross-multiplied distances from the target to
`p/q` and to `r/s`, each oriented by `v`. Given `det`, either pair follows from the
other. Expanding `m` and `n` in the residual and collapsing with `det`,

```
(p·n − m·q)·v = p(a·s + b·q)v − (a·r + b·p)qv = (p·s − r·q)·v·a = a
```

and conversely `(p·n − m·q)v·r + (m·s − r·n)v·p = m·(p·s − r·q)·v = m`. The residual
form is the one the rest of the proof consumes: it is what makes the absolute values
disappear on the algorithm's side, since `dist rs = |r·n − m·s| = b` (`dist_rs`),
leaving the only surviving absolute value on the competitor. The last row is discussed
below; it is the one clause that is not in the informal proof's list.

Each invariant holds by inspection initially (`initialLoopState`) and by direct
calculation across an iteration (`nextLoopState`), which takes a state and a proof that
the loop condition `0 < b` and `q + ⌊a/b⌋·s ≤ l` holds at it, and discharges each field
of the next state as it builds it. Note that at the end of an iteration, `s ≤ l` is
exactly the condition under which the loop was entered, namely `q + ⌊a/b⌋·s ≤ l`.

**Termination.** `a` strictly decreases every iteration, the new `a` being the old `b`
with `b < a`, and it stays nonnegative, since `0 ≤ b`. In Lean the measure is `a.toNat`
(`loop_decreases`), which is what lets `runLoop` — run the loop from a given state until
its condition fails — be an ordinary recursive definition, with
`runLoop_loopCondition_false` recording that the condition has indeed failed on exit. A
`PostLoopState` is a `LoopState` with that exit fact attached, `postLoopState` is the
one reached from `initialLoopState`, and the algorithm's answer, `limitDenominator`, is
its return value (§ "Choosing between the two candidates"). This is the function the two
listings are proved *equal* to (§ "From the listing to the algorithm"); everything in
between is about it alone.

### Why the seventh invariant

The informal proof's tie-breaking argument reasons about the *history* of the loop: "an
examination of the while loop shows that the only time `q = 0` is before entry to the
while loop", and hence that the orientation is `+1` there. That is a statement about
which states are reachable, and it is not implied by the other six invariants — a state
with `q = 0`, `s = 1`, `p = −1` and `v = −1` satisfies all six, and an algorithm
reaching it would return the *wrong* answer on a halfway tie, returning the upper bound
instead of the lower one.

Formalising a reachability argument means putting it in the invariant, and the cheapest
form is `q = 0 → v = 1`: it holds initially by inspection, and after any iteration the
new `q` is the old `s`, which is positive, so the implication is vacuous.

It is spent in exactly one place, `v_eq_one` in § "The ambiguous case", and from there
only on the statements about which of the two best approximations comes back:
`rv_eq_floor`, `limitDenominator_ambiguous_case`, and the two listing theorems. Nothing
in the specification's own vocabulary depends on it. The characterisation of the
ambiguous case reaches the pair `{⌊m/n⌋, ⌊m/n⌋ + 1}` without knowing which endpoint is
which, `endpoints_eq_floor_pair` being a disjunction over `v_cases`. That is checked
rather than argued: stubbing `v_eq_one` with `sorry` leaves all three statements about
the specification at Lean's three axioms, with no `sorryAx` among them.

## After the loop

A `PostLoopState` is a loop state whose condition has gone false. Write
`k = ⌊(l − q)/s⌋`, so that `t = p + k·r` and `u = q + k·s`, and define `c = a − k·b`.
Then, directly from the definitions and the loop invariants:

```
(t·s − r·u)·v = 1        bracket_det       (extending does not change the orientation)
(t·n − m·u)·v = c        c_eq_tu_cross     (the extended candidate's residual)
b·t + c·r = m            bt_add_cr_eq_m    (the target, recovered in the bracket basis)
b·u + c·s = n            bu_add_cs_eq_n
```

From the definition of the floor, `k ≤ (l − q)/s < k + 1`; scaling by `s` gives
`q + k·s ≤ l < q + k·s + s`, that is

```
u ≤ l < u + s
```

(`u_le_limit`, `limit_lt_s_add_u`) and hence `0 < u` (`u_pos`), since `l < u + s` and
`s ≤ l` give `u > l − s ≥ 0`. Both bounds on `u` come from that one display, and neither
needs the sign of `k`. With those, `r/s` and `t/u` are both candidates, `rs` and `tu`;
and both are in lowest terms, `bracket_det` being a Bézout identity for each of them
(`isReduced_rs`, `isReduced_tu`). That determinant is the proof's whole route to
coprimality; nothing anywhere reasons about divisibility.

For `b ≤ c` and `0 < c`, first `(k + 1)·b ≤ a` (`k_upper`), by splitting on how the loop
exited. If `b = 0` it is `0 ≤ a`, from `0 ≤ b < a`. Otherwise `0 < b` and
`l < q + ⌊a/b⌋·s`, so `⌊(l − q)/s⌋ < ⌊a/b⌋`, that is `k + 1 ≤ ⌊a/b⌋`; then
`(k+1)·b ≤ ⌊a/b⌋·b ≤ a`. So `b ≤ a − k·b = c` (`b_le_c`), and `0 < c` (`c_pos`): if
`0 < b` then `c ≥ b`, and if `b = 0` then `c = a > b = 0`.

Finally, `0 ≤ b = (m·s − r·n)·v` and `0 < c = (t·n − m·u)·v` say precisely that the
target lies between the two candidates: `r/s ≤ m/n < t/u` when `v = 1`, and
`t/u < m/n ≤ r/s` when `v = −1`. In the orientation-aware order that is `rs_lev_mn` and
`mn_lev_tu`, the second in the non-strict form the later proofs use.

## The bracket

Every candidate lies outside the bracket, or at one of its endpoints:

```
y/z ≤ r/s      or      t/u ≤ y/z          (oriented, lev_rs_or_tu_lev)
```

The identity behind it splits a candidate's denominator along the two cross-products.
Multiplying out the right-hand side leaves `z` times `(t·s − r·u)·v`, which is `1`:

```
z = (t·z − y·u)v·s + (y·s − r·z)v·u
```

A candidate strictly inside the bracket has both cross-products positive — whichever way
round the two candidates lie, the orientation flips both signs together — so both are at
least `1`, and `z ≥ s + u > l`. The Lean runs the contrapositive: from `z ≤ l < s + u`,
`(1 − (t·z − y·u)v)·s + (1 − (y·s − r·z)v)·u > 0`, so one of the two coefficients is
positive (`Int.pos_or_pos_of_lincomb_pos`), so one cross-product is at most `0`; and
`(y·s − r·z)v ≤ 0` is `y/z ≤ r/s` in the oriented order, while `(t·z − y·u)v ≤ 0` is
`t/u ≤ y/z`. This is the only case split in the rest of the argument.

**Denominators at the endpoints.** The same identity says how a candidate that *equals*
an endpoint in value can still lose to it. If `y/z = r/s` (`eqv yz rs`) then the second
cross-product vanishes and the identity reads `z = (t·z − y·u)v·s`, exhibiting `z` as a
multiple of `s` — a positive multiple, since `z` is positive — so `s ≤ z`
(`den_le_of_eqv_rs`; `Int.divisor_le_mul` is the arithmetic). Symmetrically `u ≤ z` for
a candidate equal to `t/u` (`den_le_of_tu_eqv`). The lowest-terms property of the
endpoints is doing the work here, but in its determinant form.

### Candidates outside the bracket are no closer

On the loop candidate's side, `y/z ≤ r/s ≤ m/n` in the oriented order, so the distance
from the target to `y/z` needs no absolute value: it is `(m·z − y·n)·v`
(`dist_of_lev_rs`), and the loop candidate's is `(m·s − r·n)·v = b` (`dist_rs`). The
closeness comparison `dist rs · z ≤ dist yz · s` is then

```
(m·s − r·n)v·z ≤ (m·z − y·n)v·s
```

whose two sides differ by `n·(r·z − y·s)·v`, which is nonnegative on this side. So the
loop candidate is at least as close as anything on its side, strictly so unless the two
are equal in value; and where they are, `s ≤ z` is § "The bracket"'s denominator fact,
which is the tie arm of `better`. That is `better_rs_of_lev`: the loop candidate is
better than every candidate on its side. `better_tu_of_lev` is the mirror image, through
`dist_of_tu_lev` and `dist_tu`, and putting the two together with the case split,

```
better rs yz      or      better tu yz          (better_rs_or_better_tu)
```

for every candidate `y/z`: one of the two endpoints is at least as good as it.

## Best approximations

**A best approximation is an endpoint** (`eq_rs_or_eq_tu_of_best`). Let `y/z` be best.
It lies on one side of the bracket; say the loop candidate's. Being best, it is better
than `r/s`; but `r/s` is strictly better than anything strictly on that side, so `y/z`
equals `r/s` in value. Then `s ≤ z` from the denominator fact, and `z ≤ s` from `y/z`
being better than `r/s` at equal distance, so the denominators agree; and equal in value
with equal denominators is equal as a pair (`Candidate.eq_of_eq_den`). That is
`eq_rs_of_lev_of_best`, and `eq_tu_of_lev_of_best` is its mirror image.

**Which endpoint is best.** Since one endpoint is better than any candidate and `better`
is transitive, `r/s` is best exactly when it is better than `t/u`; and with
`dist rs = b` and `dist tu = c` that unfolds to

```
best rs  ↔  b·u < c·s  or  (b·u = c·s and s ≤ u)          (rs_best_iff)
best tu  ↔  c·s < b·u  or  (c·s = b·u and u ≤ s)          (tu_best_iff)
```

## Choosing between the two candidates

Comparing `|r/s − m/n|` with `|t/u − m/n|` and scaling by `n·s·u` compares `b·u` with
`c·s`, as `rs_best_iff` says. Adding `b·u` to both sides and using `b·u + c·s = n` makes
`b·u ≤ c·s` into `2·b·u ≤ n`, which is what the code computes: the return value `rv` is
`r/s` if `2·b·u ≤ n` and `t/u` otherwise.

`rv_cases` runs the trichotomy on `b·u` against `c·s`. Below, `r/s` is returned and is
best by `rs_best_iff`. Above, `t/u` is returned and is best by `tu_best_iff`. On an
exact tie the code returns `r/s`, and its denominator really is the smaller:
`c·s = b·u ≤ c·u`, as `0 < u` and `b ≤ c`, gives `s ≤ u` on cancelling `c`
(`s_le_u_of_bu_eq_cs`), which is the tie arm of `rs_best_iff`. Either way the returned
candidate is best (`rv_best`), and `limitDenominator_best` is that statement for the
state the algorithm actually reaches.

## The ambiguous case

When is more than one candidate best? Only when both endpoints are, since every best
candidate is an endpoint; and that forces the ambiguous case
(`ambiguous_of_rs_and_tu_best`). Each endpoint being better than the other rules out the
strict arms, so the two are equidistant, with `s ≤ u` and `u ≤ s`: `s = u`. Then
`bracket_det` reads `(t − r)·v·s = 1`, so `s = 1` and `u = 1`, and `l < s + u = 2` with
`1 ≤ l` gives `l = 1`. Equidistant with `s = u = 1` and `t = r + v` puts `m/n` at
`r + v/2`, a half-integer. The Lean states that in the oriented form
`ambiguous_iff_alternative`,

```
l = 1  and  2·m·v = (2·w·v + 1)·n  for some integer w
```

which is the plain `2·m = (2·w + 1)·n` with `w` shifted by one when `v = −1`.

Now assume the ambiguous case. The limit is `1`, so `s = u = 1` (`s_eq_one`,
`u_eq_one`), and the oriented half-integer `w` with the two residual identities gives
`2·b = 2(w − r)v·n + n` and `2·c = 2(t − w)v·n − n`. Then `0 ≤ b` and `0 < c` place
`w·v` in the interval `[r·v, t·v)`, which has length one since `(t − r)·v = 1`, so
`w·v = r·v`: the half-integer is the loop candidate's numerator, oriented. Substituting
back, `2·b = n = 2·c`, so `b = c` and `b·u = c·s`. That is `consequences_of_ambiguity`,
which also records the two half-integer identities, `2·m·v = (2·r·v + 1)·n` and
`2·m·v = (2·t·v − 1)·n`, in the form with `s` and `u` still in. With `b·u = c·s` and
`s = u`, both `rs_best_iff` and `tu_best_iff` are satisfied: both endpoints are best
(`rs_best_and_tu_best`).

**Which endpoints they are.** With `v = 1`, `t = r + 1` and `2·m = (2·r + 1)·n`, so
`⌊m/n⌋ = r` (`floor_eq_of_mn_eq_add_half`): the loop candidate is `⌊m/n⌋ / 1` and the
extended one is `(⌊m/n⌋ + 1) / 1` (`endpoints_of_v_eq_one`). With `v = −1` the roles
swap, `t = r − 1` and `⌊m/n⌋ = t` (`endpoints_of_v_eq_neg_one`). Either way the pair is
`{⌊m/n⌋, ⌊m/n⌋ + 1}` (`endpoints_eq_floor_pair`), and that is all the characterisation
of the ambiguous case needs.

**Which one the code returns.** This is the one place the seventh invariant is used
(`v_eq_one`). `s = u` written out is `s = q + k·s`, so `(1 − k)·s = q`. And `b = c` with
`c = a − k·b` and `b < a` gives `0 < k·b`, so `k ≥ 1` and `0 < b`. Then `(1 − k)·s = q`
with `q ≥ 0` and `s > 0` forces `k ≤ 1`; so `k = 1` and `q = 0`, and the seventh
invariant gives `v = 1`. So the loop candidate is the floor. And the code returns the
loop candidate, since `2·b·u ≤ n` is `b·u + b·u ≤ b·u + c·s`, an equality here. That is
`rv_eq_floor`, and `limitDenominator_ambiguous_case` is the same for the state the
algorithm reaches: for example `1/2` with `l = 1`, where `0/1` and `1/1` are equally
close and `0/1` is returned.

## What the specification determines

The three results about the specification are now short.

**Uniqueness outside the ambiguous case** (`non_ambiguous_best`). Two best candidates
are both endpoints. If they were different endpoints, both endpoints would be best, and
that is the ambiguous case; so outside it they are the same. Across the bridge this is
`isBestApproximation_unique_of_not_ambiguous`.

**Exactly two inside it** (`ambiguous_best`). A candidate is best if and only if it is
`⌊m/n⌋ / 1` or `(⌊m/n⌋ + 1) / 1`: forwards by "a best approximation is an endpoint" and
`endpoints_eq_floor_pair`, backwards by `rs_best_and_tu_best`. Across the bridge,
`isBestApproximation_iff_of_ambiguous`.

**Lowest terms** (`isReduced_of_best`). A best candidate is an endpoint, and both
endpoints are reduced by the determinant. Across the bridge, and through
`Int.gcd_eq_one_of_bezout`, which turns a Bézout identity into `Int.gcd r s = 1`, this
is `isBestApproximation.gcd_eq_one`.

## From the listing to the algorithm

Everything above is about `limitDenominator`, the function on `Arguments` built from
`runLoop`. Each listing is proved *equal* to it, and its correctness is that equality
composed with `limitDenominator_best` and the bridge; its tie-break theorem is the same
equality composed with `limitDenominator_ambiguous_case`.

For the simplified listing
([`SimplifiedCorrectness.lean`](LimitDenominator/Proofs/SimplifiedCorrectness.lean)),
`loopBody` and `afterLoop` name the two halves of the `do` block, and
`limitDenominatorSimplified_fold` folds the listing onto them: past the two guards and
the initial state's two divisions, which `0 < n` makes safe, the rest is `rfl`, since
they are what the `do` block desugars to. Two lemmas reduce the body: with `b = 0`
Python's `and` short-circuits and the loop exits (`loopBody_of_zero`), and with `0 < b`
the divisions succeed and the exit test is the Python condition (`loopBody_of_pos`).
`loopTuple` projects a `LoopState` onto its seven numbers, and one body step on a
state's tuple is the tuple of `nextLoopState` where the loop condition holds and `done`
where it fails. `forIn_eq_runLoop` then identifies the `do` block's loop with `runLoop`,
by induction on `runLoop` — `fun_induction` follows the definition's own recursion —
with one `forIn_loop_peel` per iteration and `forIn_loop_done` at exit; both are in
[`WhileLoop.lean`](LimitDenominator/Proofs/WhileLoop.lean), and are the one step of
unfolding that Lean's `while` supports. `afterLoop_eq` reads the tail off as `rv`, and
`limitDenominatorSimplified_eq` puts the pieces together: the listing returns the
algorithm's numerator and denominator.

The stdlib listing
([`StdlibCorrectness.lean`](LimitDenominator/Proofs/StdlibCorrectness.lean)) takes the
same route with three differences, all from the listing's shape rather than the
algorithm's. Its state is the proof's, permuted: `(p0, q0, p1, q1, n, d)` is
`(p, q, r, s, a, b)`, and `stdlibTuple` projects in that order. Its first iteration is
peeled off (`stdlibLoopBody_initial`): the break test weighs `q0 + a·q1`, which is `1`
there, against a positive limit, so it never breaks; it divides by the target's
denominator, so it cannot raise; and the state it lands on is exactly
`initialLoopState`, which the state before it is not. And its loop condition omits
`0 < b`, so the two conditions coincide only where `b` is positive, which is where
`b_pos` comes in (§ "What the stdlib listing adds").

## What the stdlib listing adds

Everything above is written for the simplified listing. The stdlib listing runs the same
calculation on the same state, so the invariants, the bracket and the tie-breaking carry
over unchanged. Two of its differences are mathematical rather than mechanical, and both
trade on its target being in lowest terms. Both are proved by running the loop anyway:
the algorithm's exit state says what they need.

**The fast path.** When the target's denominator is already within the limit, the
shipped code returns the target itself and never reaches the loop. That answer is a best
approximation (`self_best_of_fast_path`). With `n ≤ l`, the recovery identity
`b·u + c·s = n ≤ l < s + u` says `(1 − c)·s + (1 − b)·u > 0`, so `c < 1` or `b < 1`;
`0 < c` rules out the first, so `b = 0` (`b_eq_zero_of_fast_path`). Then the two
recovery identities read `m = c·r` and `n = c·s`, making `c` a common divisor of `m` and
`n`, and lowest terms gives `c = 1`: the loop candidate *is* the target, as a pair
(`mn_eq_rs_of_b_eq_zero`). And with `b = 0` the loop candidate is best, `rs_best_iff`'s
first arm being `0 < c·s`. `isBestApproximation_self` is the translation across the
bridge, and it is what the fast path of `isCorrectLimitDenominator_stdlib` discharges
against.

**No `0 < b` test.** The shipped loop condition tests only `q2 > max_denominator`,
leaving its division by `b` unguarded. It needs no guard: past the fast path the target
is in lowest terms with `l < n`, and then `b` is never zero (`b_pos`). Were it zero at
some state, it would stay zero to the exit, since `b = 0` fails the loop condition
(`runLoop_b_eq_zero`); and at the exit `mn_eq_rs_of_b_eq_zero` gives `n = s ≤ l`, which
`l < n` denies. This is the argument of the issue's § "Optimization".

## The two listings agree

`limitDenominatorStdlib_eq_limitDenominatorSimplified`, in
[`Agreement.lean`](LimitDenominator/Proofs/Agreement.lean), says that on a target in
lowest terms with positive denominator the two listings are the same function: the same
`ValueError` below a limit of one, and the same pair above it. Its proof touches none of
the mathematics above directly, only the two correctness theorems, the two tie-break
theorems and `isBestApproximation_unique_of_not_ambiguous`. Below a limit of one both
listings raise, by the first conjunct of each correctness theorem. Above it, outside the
ambiguous case each returns a pair satisfying the specification, by the second conjunct,
and uniqueness makes those pairs equal; inside it each returns the floor, by its
tie-break theorem. So the agreement is a consequence of the specification determining
the answer, and of the two listings making the same choice where it does not, and not of
anything the listings share in shape.

## What the informal proof needs that this one does not

The informal proof establishes `2·b·q < n` at every point of the calculation and uses it
in its tie-breaking argument, to force `q < u` and hence `q = 0`. The route above
reaches `q = 0` from `s = u = 1` and `b = c` instead (§ "The ambiguous case"), so
`2·b·q < n` never appears in the Lean proof.

[issue]: https://github.com/python/cpython/issues/95723
