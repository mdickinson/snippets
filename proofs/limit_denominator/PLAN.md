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
   in the issue, which can be updated to agree.
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

/-- The one case in which `isBestApproximation` does not determine the answer. -/
def isAmbiguous (m n l : Int) : Prop := l = 1 ∧ ∃ w : Int, 2 * m = (2 * w + 1) * n
```

`isCorrectLimitDenominator` is unchanged.

## The four new public statements

All four exist already inside `Experiment.lean`; this is repackaging in the
specification's vocabulary.

```lean
theorem isBestApproximation_unique_of_not_ambiguous (hamb : ¬ isAmbiguous m n l)
    (h₁ : isBestApproximation m n l r₁ s₁) (h₂ : isBestApproximation m n l r₂ s₂) :
    r₁ = r₂ ∧ s₁ = s₂                                      -- non_ambiguous_best

theorem isBestApproximation_of_ambiguous (hamb : isAmbiguous m n l) :
    isBestApproximation m n l r s ↔
      (r, s) = (m / n, 1) ∨ (r, s) = (m / n + 1, 1)         -- ambiguous_best

theorem limitDenominatorSimplified_ambiguous (hamb : isAmbiguous m n l) :
    returns (limitDenominatorSimplified m n l) (m / n, 1)   -- rv_eq_floor
theorem limitDenominatorStdlib_ambiguous ...                -- likewise
```

Under the stdlib listing's `valid` the target is in lowest terms, so its ambiguous
case is `n = 2` with `m` odd and `l = 1`.

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
assume.** Keeping it hypothesis-free costs two small additions:

- `atLeastAsClose m n r s y z ↔ atLeastAsClose (-m) (-n) r s y z` by `Int.abs_neg`, so
  a negative `n` flips to a positive one and the machinery applies;
- `n = 0` separately: every candidate is then equidistant, so clause 2 forces `s = 1`
  and `Int.gcd_one_right` finishes it.

Fallback if that tail turns ugly: add `0 < n` to the statement and say so in README.

## `v` in the simplified listing

```python
a, b, p, q, r, s, v = n, m % n, 1, 0, m // n, 1, 1
while 0 < b and q + a // b * s <= l:
    a, b, p, q, r, s, v = b, a % b, r, s, p + a // b * r, q + a // b * s, -v
k = (l - q) // s
t, u = p + k * r, q + k * s
return (r, s) if 2 * b * u <= n else (t, u)
```

Both lines fit in 88 columns. **Checked:** no `unusedVariables` warning — `do`-block
mutables all become part of the desugared loop state, so `--wfail` is not at risk and
no `set_option` is needed. The listing's docstring goes from "two changes" to one, the
enforced preconditions, which tightens the claim that this is the issue's listing;
same edit in README beside its copy. The issue is updated to match.

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

One commit each, `lake build --wfail` and `lake lint` green at each. Steps 1 and 4 are
the only ones touching the trusted surface, and both are small enough to review alone.

1. **The specification.** `isBestApproximation` drops clause 3; `atLeastAsClose` flips;
   `isAmbiguous` is added. Adjust `gcd_eq_one` and `isBestApproximation_self` for both
   changes, drop a bullet from each of the two `Bracketing.isBestApproximation_*`, and
   flip and trim `Tests/SpecCheck.lean`'s `checkAtLeastAsClose` and `checkCandidate`.
   Delete `isBestApproximation_unique`. **This opens a window** in which the tree
   claims neither uniqueness nor the tie-break; step 3 closes most of it, step 5 the
   rest.
2. **Unify `Int.abs`.** New `Definitions/IntAbs.lean`; `Experiment.lean` drops its own
   copy and its duplicate lemmas. Clears the handoff's recorded blocker: with a
   public, exposed `Int.abs` in scope, `dist` can go public whenever wanted.
3. **The bridge**, and on it: uniqueness, the ambiguous characterisation, and
   `gcd_eq_one`'s new proof. Written into `Experiment.lean` where it stands; no
   listing touched.
4. **`v` back in the simplified listing.** The listing, its docstring, and a mechanical
   thread-through of the extra tuple component in the existing `SimplifiedCorrectness`
   — about twenty lines of churn in a file step 5 replaces, bought so that the
   trusted-surface diff can be read on its own.
5. **The simplified listing onto the new core**, plus its ambiguous-case theorem.
6. **The stdlib listing**, plus its ambiguous-case theorem. Needs `LoopState.b_pos` (the
   numerator/denominator recovery is derivable from `a_eq_pq_cross`, `b_eq_rs_cross`
   and `det`, so the existing proof transfers), the peeled first iteration, the
   permuted state, and `v` supplied from `p * s - r * q`. `isBestApproximation_self`
   still carries the fast path.
7. **Delete the dead chain.**
8. **Split and rename `Experiment.lean`** into the seven modules — a pure move,
   token-identical once whitespace is removed, as `e75e3973` was. After (7), because it
   wants the names `Bracket.lean` and `BestApproximation.lean` back.
9. **Docs.** README §§ the listing, "What is proved", "Project structure", and the
   `isBestApproximation_unique` citation in "What do I need to trust?"; PROOF.md; the
   issue's listing; PR #19's description. The largest single chunk, and prose rather
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
- **R3.** `gcd_eq_one`'s negative-`n` and zero-`n` tail, per decision 7.
- **R4.** PROOF.md. §§ "Removing the orientation from the state" (reversed outright),
  "Vocabulary", "Loop invariants", "After the loop", "The bracket", "Choosing between
  the two candidates" and "Discharging the three clauses" all describe machinery or
  decisions being replaced. §§ "The specification", "Why the seventh invariant", "What
  the stdlib listing adds" and "What the informal proof needs that this one does not"
  survive with edits.
