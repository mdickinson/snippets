# Remaining work: the stdlib listing

The simplified integer listing is done: translated, specified, proved, tested and
documented. [README.md](README.md) and [PROOF.md](PROOF.md) are the canonical documents
for it, and everything this file used to say about it now lives in one of them or in a
docstring. What is left is the second listing.

## Goal

Add `limitDenominatorStdlib`, a translation of the body of `Fraction.limit_denominator` as
it appears in CPython's `Lib/fractions.py`, and prove

```lean
theorem isCorrectLimitDenominator_stdlib :
    isCorrectLimitDenominator (fun m n => 0 < n ∧ Int.gcd m n = 1) limitDenominatorStdlib
```

The specification and the mathematics are already stated in the generality this needs: the
`valid` parameter on `isCorrectLimitDenominator` carries the extra "in lowest terms"
precondition, and `Bracketing` and everything downstream of it are independent of how the
loop produced the state. So the work is confined to a second translation plus its
mechanics, and an extension of README.md's overview, scope and trust sections.

The theorem statement above is provisional: it presumes the target stays a bare pair of
`Int`s. Settle the question below first, since it decides that statement's shape.

## Settle first: how to represent fractions

The stdlib listing is a method on a `Fraction`, so unlike the simplified listing its target
is *always* positive-denominatored and in lowest terms, and its result is built with
`Fraction._from_coprime_ints`. The obvious move is to make that structural rather than a
side condition: a type bundling numerator, denominator, `0 < den` and `gcd num den = 1`, so
the precondition is discharged at construction and cannot be forgotten at a use site. The
proof already establishes both facts about the result, so the result could inhabit it too.

Both the *how* and the *whether* are open. Points to weigh:

- **What happens to `isCorrectLimitDenominator`.** Its `valid : Int → Int → Prop` parameter
  exists precisely to carry this precondition for two listings that disagree about it. A
  fraction type could replace that parameter, or sit alongside it, or wrap only the stdlib
  listing's signature while the spec stays in `Int`s. These give noticeably different
  statements, and the statement is what a reader has to check — a spec whose hypotheses are
  invisible because they hide inside a type is not automatically the clearer one.
- **Fidelity cuts both ways.** A `Fraction`-shaped signature is closer to the Python being
  translated. But the *arithmetic* the listing performs is on bare integers, and bundling
  invariants into the loop state would be a departure, not a translation.
- **Core already has `Rat`,** with exactly these invariants (`den` positive, reduced). Reusing
  it would come free of definitional work but drags in its own API, which is thin, and its
  `den : Nat` differs from the `Int` the algorithm uses throughout.
- **Where the proof obligations land.** Bundling moves them from hypotheses to construction
  sites. That is a win at call sites and a cost inside the proof, wherever an intermediate
  pair is not yet known to be reduced.

## What is different about it

Three things, in rough order of effort.

1. **`while True` with a mid-loop `break`.** The exit is a `ForInStep.done` from the middle
   of the body rather than a false condition at the top.
   [`forIn_loop_invariant`](LimitDenominator/Proofs/WhileLoop.lean) already covers that
   shape — it takes the yield and done cases as alternatives, not as a top-of-loop test —
   but folding the desugared body onto a named `loopBody` will need its own bridge, and
   the invariant is now stated at a different point in the body.

2. **The fast path.** `Fraction.limit_denominator` returns the fraction unaltered when its
   denominator is already within the limit. That is a separate branch to discharge, and
   it is what licenses the third item.

3. **No `0 < b` test.** The shipped loop condition omits it. Issue § "Optimization" shows
   it is unnecessary: for a reduced target with `l < n` — which the fast path guarantees —
   `b` is positive at loop exit, since `b = 0` would give `a·r = m` and `a·s = n` with `m`
   and `n` coprime, hence `a = 1` and `n = s ≤ l`, contradicting `l < n`. With `b`
   positive throughout, this listing needs no short-circuiting `and` at all.

One difference deliberately *not* carried over: the simplified listing tests `n <= 0` and
raises, but the shipped code has no such test and should not gain one. It reads
`self._denominator`, which a `Fraction` keeps positive, so the translation stays faithful and
`valid` carries the precondition instead.

Also cosmetic but worth getting right: the shipped code names its variables `p0, q0, p1,
q1` and uses `n, d` for the running target. Whether to keep those names in the Lean
translation (fidelity) or rename to `p, q, r, s` (shared vocabulary with the proof layer)
is an open choice. Fidelity probably wins, with the correspondence noted in a comment.

## Tests to add

- Expected-value vectors for `limitDenominatorStdlib`, including the fast path.
- A grid cross-check `limitDenominatorStdlib m n l == limitDenominatorSimplified m n l`
  over reduced targets, which is where the two listings' agreement gets exercised.
- Re-run the Python differential test against `Fraction.limit_denominator` — the harness
  is trivial to rebuild and the current run is recorded in README.md § Testing.

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
