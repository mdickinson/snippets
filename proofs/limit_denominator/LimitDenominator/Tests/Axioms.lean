module

meta import LimitDenominator.Proofs.SimplifiedCorrectness

/-!
The axioms each correctness theorem rests on, pinned.

`lake build --wfail` already rejects an incomplete proof, since `sorry` emits a warning. It does
not reject an axiom introduced deliberately, and nothing else records what the theorems depend
on, so each one's axiom set is asserted here: `propext`, `Classical.choice` and `Quot.sound` are
Lean's own three, and any addition fails the build.

Each theorem is checked separately rather than relying on the trichotomy to cover the other two
transitively, so that a change to one proof cannot quietly narrow what is checked.
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
