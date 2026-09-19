# Rework plan — `Experiment.lean` as the core

Working document for the rework of the proof layer onto `Experiment.lean`, tracked so
that it survives between sessions. It is scaffolding, not one of the project's docs:
when step 9 lands it gets deleted, and `README.md` and `PROOF.md` are the two that
stay. Started from `a3983376`.

## Decisions taken

1. **Option A**: each listing is proved *equal* to the mathematical function, and
   correctness is that equality composed with the spec bridge.
2. **`v` stays in `LoopState`**, and goes back into the simplified listing, seventh in
   both simultaneous assignments. We control that listing — it appears publicly only
   in the issue, which carries `v` itself.
3. **`isBestApproximation` becomes two-clause.** The tie towards the floor is not a
   sense in which the floor is better; it is an implementation accident, and it moves
   out of the specification into separate statements.
4. **`isAmbiguous` is named** in `Definitions/Specification.lean`.
5. **All four new statements are public and pinned.** `Tests/Axioms.lean` goes from
   five pins to nine.
6. **`atLeastAsClose` flips** to candidate-minus-target, matching `dist`, which does
   not move. `dist`'s docstring is corrected to "from m/n to e/f" to match.
7. **The determinant becomes the canonical route to lowest terms.** `gcd_eq_one` is
   reproved through Bézout coefficients read off `bracket_det`; the spec-level proof
   is retired.
8. **Seven modules** for the core.
9. **The four new statements and `gcd_eq_one` carry `0 < n`.** Under two clauses
   `n = 0` stops being vacuous — every `(r, 1)` is then best, so uniqueness fails
   outside the ambiguous case — and for `n < 0` Lean's `m / n` is not the floor, so the
   ambiguous characterisation names the wrong pair. The project has no interest in a
   non-positive target denominator; the hypothesis says so. `gcd_eq_one` gives up a
   statement it can make today about a negative `n`, deliberately.
10. **`checkBestApproximation` gains an ambiguous-case conjunct**, replacing the clause
    it loses. Like the `Int.gcd r s == 1` conjunct beside it, it goes beyond the
    specification deliberately: it is the executable counterpart of the two
    `*_ambiguous` theorems.

## What the decisions do to the shape

Decision 3 is the big one, and it makes the rework easier rather than harder.
`Arguments.better` is *exactly* the two-clause notion — closest, then smaller
denominator — so the bridge stops being an argument and becomes an unfolding; with
decision 6 the two sides line up syntactically as well. What was the specification's
third clause is already developed in `Experiment.lean` as the ambiguous-case
analysis, and comes out as three separate statements rather than one buried clause.

Decision 2 makes the simplified listing's state an exact image of `LoopState`'s data
fields, so its half of Option A is a state identity rather than a reconstruction. The
stdlib listing is the shipped code and does not change, so its bridge still supplies
`v` itself, alongside the peeled first iteration and the permuted state.

Decision 7 forces the bridge to be an **equivalence** rather than an implication,
since the route runs *from* a spec-satisfying pair *to* the bracket endpoints. That
is a better statement anyway, and the converse direction is no harder: clause 1 gives
`better`'s first arm when strict, and on equality clause 2 supplies the denominator
comparison the second arm wants.

## What does not change

- `isCorrectLimitDenominator` keeps its two conjuncts and its name, so an
  implementation returning the ceiling in the ambiguous case is still *correct* —
  decision 3's point. What CPython actually does is pinned separately, per listing.
- `Tests/Vectors.lean`, `Tests/PythonPrimitives.lean`, `Main.lean`: untouched. No
  returned value changes anywhere in this rework.
- The seventh-invariant finding. `LoopInvariant.p_eq_one_of_q_eq_zero` becomes
  `LoopState.v_eq_one_of_q_eq_zero` — same content, keyed on `v`.

## Where the seventh invariant lands

Worth stating, because decision 3 sharpens the PR's headline rather than blunting it.

In the current tree the seventh invariant is spent on the specification's third
clause. After the rework it is spent only inside the ambiguous case: pinning `v = 1`
there, hence identifying the two best approximations as `⌊m/n⌋` and `⌊m/n⌋ + 1` and
showing the listing returns the lower. Nothing else needs it —
`ambiguous_of_rs_and_tu_best`, which is what proves the ambiguous case is the *only*
ambiguity, uses only `bracket_det`, `s_pos`, `limit_lt_s_add_u`, `one_le_limit` and
`v_cases`.

So the appeal to the loop's history is quarantined in exactly the statements about
the arbitrary choice, and the specification no longer depends on it at all.

## The specification, after

```lean
def atLeastAsClose (m n r s y z : Int) : Prop :=
  (r * n - m * s).abs * z ≤ (y * n - m * z).abs * s

def isBestApproximation (m n l r s : Int) : Prop :=
  0 < s ∧ s ≤ l ∧
  ∀ y z : Int, 0 < z → z ≤ l →
    atLeastAsClose m n r s y z
    ∧ (atLeastAsClose m n y z r s → s ≤ z)

/--
The one case in which `isBestApproximation` does not determine the answer, for a
positive target denominator. (For `n = 0` every `(r, 1)` is best, whatever the limit.)
-/
def isAmbiguous (m n l : Int) : Prop := l = 1 ∧ ∃ w : Int, 2 * m = (2 * w + 1) * n
```

`isCorrectLimitDenominator` is unchanged.

`Tests/SpecCheck.lean`'s Bool form of the new definition, decision 10:

```lean
def checkAmbiguous (m n l : Int) : Bool :=
  l == 1 && 2 * m % n == 0 && (2 * m / n) % 2 == 1
```

with `checkBestApproximation` gaining `!checkAmbiguous m n l || (r == m / n && s == 1)`.
Both readings of `%` want the grid's `0 < n`, which the existing `y := m * z / n` wants
too; the odd-quotient test is sign-safe either way, `%` on `Int` being `emod`.

## The four new public statements

All four exist already inside `Experiment.lean`; this is repackaging in the
specification's vocabulary.

```lean
theorem isBestApproximation_unique_of_not_ambiguous (hn : 0 < n)
    (hamb : ¬ isAmbiguous m n l)
    (h₁ : isBestApproximation m n l r₁ s₁) (h₂ : isBestApproximation m n l r₂ s₂) :
    r₁ = r₂ ∧ s₁ = s₂                                      -- non_ambiguous_best

theorem isBestApproximation_of_ambiguous (hn : 0 < n) (hamb : isAmbiguous m n l) :
    isBestApproximation m n l r s ↔
      (r, s) = (m / n, 1) ∨ (r, s) = (m / n + 1, 1)         -- ambiguous_best

theorem limitDenominatorSimplified_ambiguous (hn : 0 < n) (hamb : isAmbiguous m n l) :
    returns (limitDenominatorSimplified m n l) (m / n, 1)   -- rv_eq_floor
theorem limitDenominatorStdlib_ambiguous ...                -- likewise, under `valid`
```

Every one of them needs `0 < n`, per decision 9; the two listing statements take it
from `valid` anyway.

Under the stdlib listing's `valid` the target is in lowest terms, so its ambiguous case
is `n = 2` with `m` odd and `l = 1` — which fails `n ≤ l`, so the fast path is never the
ambiguous one, and that theorem lives wholly on the loop path.

## The bridge

```lean
theorem best_iff_isBestApproximation {args : Arguments} (ef : args.Candidate) :
    args.best ef ↔ isBestApproximation args.m args.n args.limit ef.num ef.den
```

Forwards: clause 1 is either arm of `better ef gh`; clause 2 kills the strict arm and
reads `s ≤ z` off the other. Backwards: clause 1 strict gives the first arm, and on
equality clause 2 gives the second. With decision 6 both directions are unfoldings.

## Lowest terms, the new route

```lean
theorem Int.gcd_eq_one_of_bezout {g h r s : Int} (hb : g * r + h * s = 1) :
    Int.gcd r s = 1
```

cheap: `(gcd r s : Int)` divides `r` and `s`, hence divides `1`. The reverse direction
is *not* available — core has no extended-gcd Bézout identity (no `gcdA`, no
`gcd_eq_gcd_ab`), and this project is Mathlib-free — so the determinant route is the
only constructive one.

`isBestApproximation.gcd_eq_one` then runs: spec → `best` (the bridge, backwards) →
`eq_rs_or_eq_tu_of_best` → coefficients off `bracket_det` → `Int.gcd_eq_one_of_bezout`.

**This needs `0 < n`, to build the `Arguments`, which the current statement does not
assume.** Per decision 9 it gains that hypothesis rather than a tail covering the other
signs: no negation lemma carrying a negative `n` to a positive one, and no separate
`n = 0` case where every candidate is equidistant and clause 2 forces `s = 1`. The
theorem stops saying anything outside `0 < n`, which is where the project's interest
stops too.

The hypothesis lands at step 3, with the proof that uses it. Added at step 1, on top of
the existing proof, it would be an unused binder — `unusedVariables` warns, and
`--wfail` turns that into a failure.

## `v` in the simplified listing

```python
a, b, p, q, r, s, v = n, m % n, 1, 0, m // n, 1, 1
while 0 < b and q + a // b * s <= l:
    a, b, p, q, r, s, v = b, a % b, r, s, p + a // b * r, q + a // b * s, -v
k = (l - q) // s
t, u = p + k * r, q + k * s
return (r, s) if 2 * b * u <= n else (t, u)
```

Both Python lines fit in 88 columns, at 58 and 84 characters. The Lean does not: the
loop body's simultaneous assignment goes from 84 characters to 91, so that one line
wraps.

**Checked:** no `unusedVariables` warning — `do`-block mutables all become part of the
desugared loop state, so `--wfail` is not at risk and no `set_option` is needed. The
listing's docstring goes from "two changes" to one, the enforced preconditions, which
tightens the claim that this is the issue's listing; same edit in README beside its
copy.

The issue already carries `v` in its invariants, so this closes a divergence rather
than opening one, and no edit there is needed for the two listings to agree.

## Target layout

| Module | Contents |
| --- | --- |
| `Definitions/IntAbs.lean` | `Int.abs` alone, imported by the spec and by the proofs |
| `Definitions/Specification.lean` | two-clause `isBestApproximation`, flipped `atLeastAsClose`, `isAmbiguous` |
| `Proofs/SupportLemmas.lean` | `Int.abs` lemmas, the arithmetic facts, the gcd/dvd facts |
| `Proofs/FractionPair.lean` | `FractionPair`, `isHalfInteger`, the mul-den algebra |
| `Proofs/Arguments.lean` | `Arguments`, `Candidate`, `dist`/`better`/`best`, `ambiguous`, `floor` |
| `Proofs/LoopState.lean` | `LoopState`, `initialLoopState`, `nextLoopState`, `runLoop`, `b_pos` |
| `Proofs/Bracket.lean` | `PostLoopState`, `k`/`t`/`u`, `lev`/`eqv`, the bracket, distances |
| `Proofs/Algorithm.lean` | `rv`, the ambiguous case, `postLoopState`, `limitDenominator` |
| `Proofs/BestApproximation.lean` | the specification's vocabulary: the bridge, the four statements, `gcd_eq_one`, `isBestApproximation_self` |
| `Proofs/WhileLoop.lean` | gains a "the loop stops here" lemma; loses `forIn_loop_invariant` if nothing needs it |
| `Proofs/PythonTranslation.lean` | unchanged |
| `Proofs/SimplifiedCorrectness.lean` | rewritten: fold, induct, read off |
| `Proofs/StdlibCorrectness.lean` | the same, with `v` supplied, peeled and permuted |

## What dies

- `LoopInvariant.lean`, `AfterLoop.lean`, `TieBreak.lean`, and `Bracket.lean`'s current
  contents (the name is reused).
- `BestApproximation.lean`'s `Bracketing` half: `isBestApproximation_loop`, `_extended`
  and the two `_of_test` wrappers; and `gcd_eq_one`'s spec-level proof.
- `isBestApproximation_unique` as it stands — false under two clauses, and back in
  two parts.
- From `SupportLemmas.lean`: `Int.le_mul_of_one_le_left`, `Int.abs_cancel`,
  `Int.abs_lt_abs_of_mul_lt_mul`, which serve the bracket manoeuvres that `lev`/`eqv`
  and `dist_of_lev_rs` replace; and `Int.abs_mul_of_pos` if `gcd_eq_one` was its only
  caller.
- `forIn_loop_invariant`, if Option A holds for both listings.

Not a line-count win: the two developments are comparable in size. The win is one
vocabulary instead of two, a specification that says only what it means, and results
the current proof does not have — uniqueness, the ambiguous characterisation, and the
two listings agreeing as a theorem rather than as a test.

## Order of work

One commit each, `lake build --wfail` and `lake lint` green at each. Steps 1, 3 and 4
touch the trusted surface — step 1 the specification, step 3 the first two new
statements and `gcd_eq_one`'s hypothesis, step 4 the listing — and each is small enough
to review alone.

1. **The specification.** `isBestApproximation` drops clause 3; `atLeastAsClose` flips;
   `isAmbiguous` is added. Adjust `gcd_eq_one` and `isBestApproximation_self` for both
   changes, keeping both statements as they stand, drop a bullet from each of the two
   `Bracketing.isBestApproximation_*`, and flip and trim `Tests/SpecCheck.lean`'s
   `checkAtLeastAsClose` and `checkCandidate`,
   which gains `checkAmbiguous` and decision 10's conjunct. Delete
   `isBestApproximation_unique`.

   The flip is not free in the layer that is about to die. `Bracket.lean` hands out its
   bounds in the old orientation, on `(m * s - r * n).abs`, and `omega` and `grind`
   treat `.abs` as an atom, so the two `Bracketing.isBestApproximation_*` proofs need
   rewriting through `Int.abs_neg` to take them; `gcd_eq_one` needs its residual
   equation negated. Throwaway work on code step 7 deletes, and the price of a
   trusted-surface diff that can be read on its own.

   **This opens a window** in which the tree proves neither uniqueness nor the
   tie-break; step 3 closes most of it, step 5 the rest. Behaviour stays covered
   throughout: `Tests/Vectors.lean` pins all four ambiguous cases, and decision 10's
   conjunct keeps `SpecCheck` testing the tie direction across the window.
2. **Unify `Int.abs`.** New `Definitions/IntAbs.lean`; `Experiment.lean` drops its own
   copy and its duplicate lemmas. Clears the handoff's recorded blocker: with a
   public, exposed `Int.abs` in scope, `dist` can go public whenever wanted.
3. **The bridge**, and on it: uniqueness, the ambiguous characterisation, and
   `gcd_eq_one`'s new proof. Written into `Experiment.lean` where it stands; no
   listing touched. `gcd_eq_one` gains its `0 < n` here, with the proof that uses it.
   The first two of decision 5's four pins land here.
4. **`v` back in the simplified listing.** The listing, its docstring, and a mechanical
   thread-through of the extra tuple component in the existing `SimplifiedCorrectness`
   — about twenty lines of churn in a file step 5 replaces, bought so that the
   trusted-surface diff can be read on its own.
5. **The simplified listing onto the new core**, plus its ambiguous-case theorem and
   its pin.
6. **The stdlib listing**, plus its ambiguous-case theorem. Needs `LoopState.b_pos` (the
   numerator/denominator recovery is derivable from `a_eq_pq_cross`, `b_eq_rs_cross`
   and `det`, so the existing proof transfers), the peeled first iteration, the
   permuted state, and `v` supplied from `p * s - r * q`. `isBestApproximation_self`
   still carries the fast path, which the ambiguous-case theorem — the last pin — never
   reaches.
7. **Delete the dead chain.**
8. **Split and rename `Experiment.lean`** into the seven modules. Not a pure move:
   `Experiment.lean` carries no `public` or `@[expose]` marker anywhere today, which is
   what lets its own `Int.abs` coexist with the specification's. The split makes most
   of its declarations public, and `@[expose]` every definition another module unfolds
   — `Arguments.dist`, `better`, `ambiguous`, `floor`, `floorAddOne`, `isHalfInteger`
   and `LoopState.loopCondition` at least. The lint gate then applies to them, and
   `ambiguous`, `floor`, `floorAddOne`, `u`, `rs`, `tu` and `lev` have block comments
   where they will need docstrings. After (7), because it wants the names
   `Bracket.lean` and `BestApproximation.lean` back.
9. **Docs.** README §§ the listing, "What is proved", "Project structure" — which has
   no `Experiment.lean` row even now — "`while` loops and simultaneous assignment",
   whose six-tuple and `forIn_loop_invariant` citation both go, and the
   `isBestApproximation_unique` citation in "What do I need to trust?", where the
   replacement is a two-part claim of equal strength and should be spelled out as one,
   and where `gcd_eq_one`'s new hypothesis wants a line of its own. Then PROOF.md and
   PR #19's description. The largest single chunk, and prose rather
   than proof.
10. **Optional.** The two listings agree, as a theorem. Needs
    `args.limitDenominator = args.mn` when `n ≤ limit` and the target is in lowest
    terms, to cover the stdlib fast path.

## Risks

- **R1.** `fun_induction runLoop` inside a goal about `forIn`. The only significant
  unknown left; decision 3 took the other one away. `runLoop_loopCondition_false`
  already does `fun_induction runLoop`, so the induction principle works. Fallback is
  per-listing: the invariant-threading route still exists for whichever listing fights.
- **R2.** The stdlib listing under Option A: `v` reconstructed, the first iteration
  peeled, the state permuted, and the loop condition coinciding only under `b_pos`.
  Smaller than it looks: `b_pos` is state-local, `a * r + b * p = m` and
  `a * s + b * q = n` coming back from `a_eq_pq_cross`, `b_eq_rs_cross` and `det`, and
  its two hypotheses — lowest terms, and `limit < n` — are about `args`, so the
  induction threads nothing that varies.
- **R3.** PROOF.md. §§ "Removing the orientation from the state" (reversed outright),
  "Vocabulary", "Loop invariants", "After the loop" with "The degenerate tie", "The
  bracket", "Choosing between the two candidates" and "Discharging the three clauses"
  all describe machinery or decisions being replaced. §§ "The specification", "Why the
  seventh invariant", "What the stdlib listing adds" and "What the informal proof needs
  that this one does not" survive with edits.
