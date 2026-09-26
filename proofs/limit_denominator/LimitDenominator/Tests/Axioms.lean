module

meta import LimitDenominator.Proofs.Agreement
meta import LimitDenominator.Proofs.Experiment
meta import LimitDenominator.Proofs.SimplifiedCorrectness
meta import LimitDenominator.Proofs.StdlibCorrectness

/-!
The axioms each correctness theorem rests on, pinned.

`lake build --wfail` already rejects an incomplete proof, since `sorry` emits a warning. It does
not reject an axiom introduced deliberately, and nothing else records what the theorems depend
on, so each one's axiom set is asserted here: `propext`, `Classical.choice` and `Quot.sound` are
Lean's own three, and any addition fails the build.

Each theorem is checked separately rather than relying on the trichotomy to cover the other two
transitively, so that a change to one proof cannot quietly narrow what is checked.

`isBestApproximation.gcd_eq_one` is pinned alongside them because the specification does not
stipulate lowest terms: that promise is carried by this theorem alone. The two statements about
what the specification does and does not determine — one solution outside the ambiguous case,
exactly two inside it — are pinned for the same reason, being claims no correctness theorem
makes. So is the tie-break, once per listing: where the specification admits both
answers, which one comes back is a claim about that listing alone. And the two listings'
agreement is pinned last, being the one statement made about both at once.
-/

/--
info: 'isCorrectLimitDenominator_simplified' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isCorrectLimitDenominator_simplified

/--
info: 'limitDenominatorSimplified_raises_of_denominator_nonpos' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms limitDenominatorSimplified_raises_of_denominator_nonpos

/--
info: 'limitDenominatorSimplified_total' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms limitDenominatorSimplified_total

/--
info: 'limitDenominatorSimplified_returns_floor_of_ambiguous' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms limitDenominatorSimplified_returns_floor_of_ambiguous

/--
info: 'isCorrectLimitDenominator_stdlib' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isCorrectLimitDenominator_stdlib

/--
info: 'limitDenominatorStdlib_returns_floor_of_ambiguous' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms limitDenominatorStdlib_returns_floor_of_ambiguous

/--
info: 'isBestApproximation.gcd_eq_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isBestApproximation.gcd_eq_one

/--
info: 'isBestApproximation_unique_of_not_ambiguous' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isBestApproximation_unique_of_not_ambiguous

/--
info: 'isBestApproximation_iff_of_ambiguous' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isBestApproximation_iff_of_ambiguous

/--
info: 'limitDenominatorStdlib_eq_limitDenominatorSimplified' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms limitDenominatorStdlib_eq_limitDenominatorSimplified
