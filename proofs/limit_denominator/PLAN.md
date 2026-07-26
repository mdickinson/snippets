# Remaining work: proving the stdlib listing

The simplified integer listing is done: translated, specified, proved, tested and
documented. [README.md](README.md) and [PROOF.md](PROOF.md) are the canonical documents for
it, and everything this file used to say about it now lives in one of them or in a docstring.

The stdlib listing is now translated and tested, in
[`LimitDenominatorStdlib.lean`](LimitDenominator/Definitions/LimitDenominatorStdlib.lean) and
[`Tests/LimitDenominatorStdlib.lean`](LimitDenominator/Tests/LimitDenominatorStdlib.lean).
What is left is its proof, and the documentation that waits on it.

## Goal

Prove `limitDenominatorStdlib` correct:

```lean
theorem isCorrectLimitDenominator_stdlib :
    isCorrectLimitDenominator (fun m n => 0 < n ∧ Int.gcd m n = 1) limitDenominatorStdlib
```

The specification and the mathematics are already stated in the generality this needs: the
`valid` parameter on `isCorrectLimitDenominator` carries the extra "in lowest terms"
precondition, and `Bracketing` and everything downstream of it are independent of how the
loop produced the state. So the work is confined to the loop mechanics and the fast path.

Then the documentation, which still describes only the simplified listing as proved:
README.md's overview (its closing paragraph says so outright), § Scope, § "What is proved",
§ "What do I need to trust?" and § Testing, and a pin for the new theorem in
[`Tests/Axioms.lean`](LimitDenominator/Tests/Axioms.lean).

## Settled: fractions stay bare `Int`s

The stdlib listing is a method on a `Fraction`, so unlike the simplified listing its target
is *always* positive-denominatored and in lowest terms, and its result is built with
`Fraction._from_coprime_ints`. A type bundling numerator, denominator, `0 < den` and
`gcd num den = 1` would make that structural rather than a side condition. It was weighed
and rejected: the signature stays three `Int`s in and an `Int × Int` out, with
`isCorrectLimitDenominator`'s `valid` parameter carrying the precondition, as the theorem
above states.

- **A bundled type would put a proof in the Definitions layer.**
  `Fraction._from_coprime_ints` is CPython's *unchecked* constructor: its docstring says the
  ratio "should be" in lowest terms with a positive denominator, and it verifies neither. The
  obligation it skips is `Int.gcd r s = 1`, one of the three things this project proves, so a
  proof field of that shape could not be filled at the return sites without a coprimality
  proof inside [`Definitions`](LimitDenominator/Definitions) — which holds no theorem and no
  tactic block today, and is the one layer README § "What do I need to trust?" asks a reader
  to read. Bundling would move the theorem into the definition.
- **`valid` keeps the precondition where a reader checks it.** What that gives up is a use
  site's inability to forget the precondition — but there are no use sites, and a visible
  hypothesis beats one hidden inside a type.
- **The two listings then share a specification verbatim,** which is what makes the grid
  cross-check `limitDenominatorStdlib m n l == limitDenominatorSimplified m n l` below
  well-typed.
- **Core's `Rat`** is rejected on its `den : Nat` against the `Int` the algorithm uses
  throughout; `Rat.mk'` would also demand the same proofs.

One thing the decision does not rule out: a fraction structure defined in the *proof* layer,
with a `limitDenominator` on it built from the `Int`-level function together with
`isCorrectLimitDenominator_stdlib` to discharge its coprimality field — `_from_coprime_ints`'s
informal "trust me" replaced by the proof, at no cost to the trusted layer. Not agreed; ask
before building it.

## What is different about it

The Python being translated is quoted in the module docstring of
[`LimitDenominatorStdlib.lean`](LimitDenominator/Definitions/LimitDenominatorStdlib.lean),
beside the Lean. Three things about it are different, in rough order of effort.

1. **`while True` with a mid-loop `break`.** The exit is a `ForInStep.done` from the middle
   of the body rather than a false condition at the top.
   [`forIn_loop_invariant`](LimitDenominator/Proofs/WhileLoop.lean) already covers that
   shape — it takes the yield and done cases as alternatives, not as a top-of-loop test —
   but folding the desugared body onto a named `loopBody` will need its own bridge. The
   invariant itself should carry over unchanged, for the reason in
   [Peeling the first iteration](#peeling-the-first-iteration) below.

2. **The fast path.** `Fraction.limit_denominator` returns the fraction unaltered when its
   denominator is already within the limit. That is a separate branch to discharge, and
   it is what licenses the third item. It needs no new mathematics:
   `isBestApproximation m n l m n` for a reduced target with `0 < n ≤ l` comes from
   [`Int.le_of_mul_eq_mul_of_gcd_eq_one`](LimitDenominator/Proofs/SupportLemmas.lean), since a
   competitor `y / z` that is also at distance zero satisfies `y·n = m·z`.

3. **No `0 < b` test.** The shipped loop condition omits it. Issue § "Optimization" shows
   it is unnecessary: for a reduced target with `l < n` — which the fast path guarantees —
   `b` is positive at loop exit, since `b = 0` would give `a·r = m` and `a·s = n` with `m`
   and `n` coprime, hence `a = 1` and `n = s ≤ l`, contradicting `l < n`. With `b`
   positive throughout, this listing needs no short-circuiting `and` at all.

One difference deliberately *not* carried over: the simplified listing tests `n <= 0` and
raises, but the shipped code has no such test and should not gain one. It reads
`self._denominator`, which a `Fraction` keeps positive, so the translation stays faithful and
`valid` carries the precondition instead.

Also worth getting right: the shipped code names its variables `p0, q0, p1, q1` and uses
`n, d` for the running target — so in *that* listing `n` is the numerator, where the
specification and the simplified listing use `n` for the denominator. That collision argues
strongly for fidelity over shared vocabulary with the proof layer, since a signature
`(m n l : Int)` would force the body to shadow `n` with the numerator. So: name the
parameters after the Python attributes (`numerator`, `denominator`, `maxDenominator`), keep
`p0, q0, p1, q1, n, d, a, q2, k` as shipped, and note the correspondence in a comment.

### Peeling the first iteration

The correspondence is closer than it looks, because the first iteration of the stdlib
listing's loop is unconditional and computes exactly the simplified listing's initialisation.
Its break test is `q2 > max_denominator` with `q2 = q0 + a·q1 = 1 + a·0 = 1`, and `0 < l` is
already in hand, so it cannot fire; its division is by the target's denominator, so it cannot
raise. Writing the target as `m/n` — this document's convention, not the shipped code's — the
state after that iteration is the simplified listing's initial state, permuted:

    p0, q0, p1, q1  =  p, q, r, s  =  1, 0, m//n, 1
    n, d            =  a, b        =  n, m % n

and it stays permuted that way, iteration for iteration: `a = n//d` is `a // b`;
`p0, q0, p1, q1 = p1, q1, p0+a*p1, q2` is `p, q, r, s := r, s, p + a//b*r, q + a//b*s`;
`n, d = d, n-a*d` is `a, b := b, a % b`; and `q2 > max_denominator` is the negation of
`q + a//b*s <= l`. After the loop, `k` is `(l - q)//s`, `(p0+k*p1, q0+k*q1)` is `(t, u)`,
`(p1, q1)` is `(r, s)`, and `2*d*(q0+k*q1) <= self._denominator` is `2*b*u <= n`.

So peeling one iteration with `forIn_eq_of_monadTail` should let
[`LoopInvariant`](LimitDenominator/Proofs/LoopInvariant.lean) be reused verbatim rather than
restated at a new point in the body. It *has* to be peeled: at the shipped initial state the
invariant's `s_pos`, `q_le_s` and `b_lt_a` all fail, `s` there being `q1 = 0`.

## Tests

Done, in [`Tests/LimitDenominatorStdlib.lean`](LimitDenominator/Tests/LimitDenominatorStdlib.lean):
expected-value vectors including the fast path, the `ValueError`, `checkBestApproximation`
over the reduced targets of `specCheckGrid`, and agreement with `limitDenominatorSimplified`
over those same targets.

Both grid checks are gated on `Int.gcd m n = 1`, so both could have passed vacuously. They do
not: a clear majority of the grid's targets are reduced, and among those both tie-break clauses
have live antecedents for negative and positive `m` alike — clause 3's being exactly the
limit-of-one, halfway-between-integers family that § "The degenerate tie" of
[PROOF.md](PROOF.md) shows is the only one there is. To re-derive: filter `specCheckGrid` to
reduced targets and count those with a rival that ties on distance at a different denominator
(clause 2) or at the same one (clause 3).

Separately, and not in the build: while the translation was being written it was
differential-tested against `Fraction.limit_denominator` in CPython 3.14 over 94,207 cases —
reduced targets with `1 ≤ n ≤ 40`, `−80 ≤ m ≤ 80` and `1 ≤ l ≤ 24`, plus README.md's examples
and a few wide ones — with identical output throughout. README.md § Testing's recorded run is
a different test, of the *Python* simplified listing, and is unaffected.

## Open item

**A command-line executable** was proposed but never agreed. isqrt has one (`lake exe
isqrt N`), and the shape would be the same here: take `m n l`, print `r/s`, and lean on
the correctness proof to omit handling for the impossible exception case. It would add a
`lean_exe` to [`lakefile.toml`](lakefile.toml), a `Main.lean`, and a section to
README.md. Not built; ask before building it.

## Vocabulary

[PROOF.md](PROOF.md) § Vocabulary fixes the terms the proof uses, and the Lean names match
it. Two more terms are needed once there are two listings, and are used that way
throughout README.md:

**Simplified listing** — the three-argument integer function from
[cpython#95723][issue], against which the informal proof is written. Lean:
`limitDenominatorSimplified`. *Avoid*: reference listing, toy version, model.

**Stdlib listing** — the body of `Fraction.limit_denominator` as shipped. Lean:
`limitDenominatorStdlib`. *Avoid*: shipped listing, real version, production version,
actual code.

[issue]: https://github.com/python/cpython/issues/95723
