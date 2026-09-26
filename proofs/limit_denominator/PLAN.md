# Rework plan — `Experiment.lean` as the core

Working document for the rework of the proof layer onto `Experiment.lean`, tracked so
that it survives between sessions. It is scaffolding, not one of the project's docs:
it gets deleted once the last step has landed, and `README.md` and `PROOF.md` are the
two that stay.

## Progress

Steps 1 to 7 have landed; their commits carry the reasoning, and the tree is the
record of what they produced, so the sections that described them have been cut. What
they changed about the steps still to come is folded in below.

Step 8, the split, is deferred (decision 13): steps 9 and 10 come first, against the
unsplit tree, and the split is reconsidered once they have landed. Step 9 has landed;
step 10 is next.

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
5. **All four new statements are public and pinned.** `Tests/Axioms.lean` ends with
   nine pins.
6. **`atLeastAsClose` flips** to candidate-minus-target, matching `dist`, which does
   not move. `dist`'s docstring is corrected to "from m/n to e/f" to match.
7. **The determinant becomes the canonical route to lowest terms.** `gcd_eq_one` is
   reproved through Bézout coefficients read off `bracket_det`; the spec-level proof
   is retired.
8. **The core is split into per-layer modules**, the ones the target layout lists.
9. **The four new statements and `gcd_eq_one` carry `0 < n`.** Under two clauses
   `n = 0` stops being vacuous — every `(r, 1)` is then best, so uniqueness fails
   outside the ambiguous case — and for `n < 0` Lean's `m / n` is not the floor, so the
   ambiguous characterisation names the wrong pair. The project has no interest in a
   non-positive target denominator; the hypothesis says so. `gcd_eq_one` gives up a
   statement it can make today about a negative `n`, deliberately.
10. **`checkBestApproximation` gains an ambiguous-case conjunct**, replacing the clause
    it loses. Like the `Int.gcd r s == 1` conjunct beside it, it goes beyond the
    specification deliberately: it is the executable counterpart of the two listing
    theorems.
11. **The proof core does not import the specification.** `Arguments.ambiguous` and
    `isAmbiguous` are the same formula, stated twice rather than one delegating to the
    other, so that the core meets the trusted surface at `BestApproximation.lean`
    alone. `ambiguous_iff_isAmbiguous` records the coincidence there.
12. **Private by default.** A declaration is `public` only where a consumer names it,
    and `@[expose]` only where a consumer unfolds it. No blanket `public section` — it
    would make the whole core API, and nothing could then be changed without checking
    every module. The rule outlives the split; step 8 applies it per module.
13. **The split waits.** Steps 9 and 10 land against the unsplit tree, so that proofs,
    docs and PR are complete and self-consistent first; step 8's layout is then
    reconsidered rather than assumed. Step 9's docs describe `Experiment.lean` as it
    is, and the split, in whatever shape, will touch the docs again.

## What the decisions do to the shape

Decision 3 is the big one, and it makes the rework easier rather than harder.
`Arguments.better` is *exactly* the two-clause notion — closest, then smaller
denominator — so the bridge stops being an argument and becomes an unfolding; with
decision 6 the two sides line up syntactically as well. What was the specification's
third clause is already developed in `Experiment.lean` as the ambiguous-case
analysis, and comes out as three separate statements rather than one buried clause.

Decision 2 makes the simplified listing's state an exact image of `LoopState`'s data
fields. Option A runs its induction on `runLoop`, so for both listings the tuple is a
projection of the loop state and neither reconstructs anything — the stdlib listing's
six components are the projection that omits `v`. What its bridge still owes is the
peeled first iteration and the permuted state.

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

## Target layout

| Module | Contents |
| --- | --- |
| `Definitions/IntAbs.lean` | `Int.abs` alone, imported by the spec and by the proofs |
| `Definitions/Specification.lean` | two-clause `isBestApproximation`, flipped `atLeastAsClose`, `isAmbiguous` |
| `Proofs/SupportLemmas.lean` | `Int.abs` lemmas, the arithmetic facts, the positive-factor family, `Int.gcd_eq_one_of_bezout` |
| `Proofs/Arguments.lean` | `Arguments`, `Candidate` with `isReduced` and `eq_of_eq_den`, `dist`/`better`/`best`, `ambiguous`, `floor` |
| `Proofs/LoopState.lean` | `LoopState`, `initialLoopState`, `nextLoopState`, `runLoop` |
| `Proofs/Bracket.lean` | `PostLoopState`, `k`/`t`/`u`, `lev`/`eqv`, the bracket, distances |
| `Proofs/Algorithm.lean` | `rv`, the ambiguous case, `postLoopState`, `limitDenominator`, `b_pos`, `self_best_of_fast_path` |
| `Proofs/BestApproximation.lean` | the specification's vocabulary: the bridge, the four statements, `gcd_eq_one`, `isBestApproximation_self` |
| `Proofs/WhileLoop.lean` | unchanged: `forIn_loop_peel` and `forIn_loop_done` |
| `Proofs/PythonTranslation.lean` | unchanged |
| `Proofs/SimplifiedCorrectness.lean` | rewritten: fold, induct, read off |
| `Proofs/StdlibCorrectness.lean` | the same, peeled and permuted |

## What the rework buys

Not a line-count win: the two developments are comparable in size. The win is one
vocabulary instead of two, a specification that says only what it means, and results
the current proof does not have — uniqueness, the ambiguous characterisation, and the
two listings agreeing as a theorem rather than as a test.

## Order of work

One commit each, `lake build --wfail` and `lake lint` green at each. Steps 1, 3 and 5
touch the trusted surface — step 1 the specification, step 3 the first two new
statements and `gcd_eq_one`'s hypothesis, step 5 the listing — and each is small enough
to review alone.

1. **The specification.** Landed.
2. **Unify `Int.abs`.** Landed.
3. **The bridge**, and on it: uniqueness, the ambiguous characterisation, and
   `gcd_eq_one`'s new proof. Landed, at the end of `Experiment.lean`, which imports
   `Definitions.Specification` for that section alone.
4. **The simplified listing onto the new core**, plus its ambiguous-case theorem and
   its pin. Landed. It opened the core's API: thirty of `Experiment.lean`'s
   declarations are `public` and eleven of those `@[expose]`, each one because
   `SimplifiedCorrectness.lean` names it or unfolds it, and the rest of the file stays
   private. The sixteen docstrings the lint gate then wanted are written.
5. **`v` back in the simplified listing.** Landed. The enforced preconditions are now
   the listing's only divergence from the issue's, which README and PROOF.md both say.
6. **The stdlib listing**, plus its ambiguous-case theorem. Needs `LoopState.b_pos` (the
   numerator/denominator recovery is derivable from `a_eq_pq_cross`, `b_eq_rs_cross`
   and `det`, so the existing proof transfers), the peeled first iteration and the
   permuted state. Landed. `LoopState.b_pos` and `isBestApproximation_self` moved into
   the core, the latter into the closing specification section; `Tests/Axioms.lean`
   ends with its nine pins, as decision 5 said it would.
7. **Delete the dead chain.** Landed, and it took `SupportLemmas.lean` with it:
   `Int.le_mul_of_one_le_left`, `Int.abs_neg`, `Int.abs_of_nonneg`, `Int.abs_mul_of_pos`,
   `Int.abs_cancel` and `Int.abs_lt_abs_of_mul_lt_mul` had no reachable callers left,
   and `Int.dvd_of_mul_eq_mul_of_gcd_eq_one` is down to one in-file caller and so is
   private now. What survives is checked used, one grep per name.
8. **Split and rename `Experiment.lean`** into the modules the target layout lists.
   Not a pure move: the markers move with the declarations, and the split turns what
   is one module boundary into eight, so each one is decided again — some of what is
   public today is public only for `SimplifiedCorrectness`, and some of what is
   private today is named across a boundary the split creates. Both directions, and
   each new `public` costs a docstring. The imports are decided again too: the core's
   `public import` of `SupportLemmas` can already be a plain one, nothing downstream
   needing those names through it. After (7), because it wants the names `Bracket.lean`
   and `BestApproximation.lean` back.

   It also moves the closing specification section to `BestApproximation.lean` and
   drops the `Definitions.Specification` import step 3 added, which is what makes
   decision 11 true of the split layout, and takes `Tests/Axioms.lean`'s import of
   `Experiment` away again.
9. **Docs.** README and PROOF.md landed, describing the unsplit tree per decision 13.
   PROOF.md is largely rewritten around `Experiment.lean`'s route — the oriented order,
   `rs_best_iff`, the ambiguous case, the exit-state fast path — and its § "Why the
   seventh invariant" now carries the quarantine argument this file used to, with the
   `sorry`-stubbing check re-run on the reworked core. PR #19's description follows
   the same shape and flags `Experiment.lean`'s name as provisional and this file as
   scaffolding; step 10 adds its theorem there.
10. **The two listings agree**, as a theorem. No new lemma about the
    algorithm is needed. On the slow path both listings equal `args.limitDenominator`
    by Option A. On the fast path the stdlib pair `(m, n)` is best by
    `self_best_of_fast_path`, the simplified return is best by `limitDenominator_best`,
    and `non_ambiguous_best` closes the gap — ambiguity being
    excluded there because `0 < n ≤ l = 1` forces `n = 1`, and `2m = 2w + 1` has no
    solution. Lowest terms is not needed for that exclusion; it stays load-bearing
    only through `self_best_of_fast_path`. The exclusion is
    `not_ambiguous_of_fast_path`, deleted for want of a caller and wanted back here.
    The theorem needs a home that imports both correctness modules, and
    `limitDenominatorSimplified_eq`, `limitDenominatorStdlib_eq` and
    `non_ambiguous_best` become `public` for it, per decision 12.
