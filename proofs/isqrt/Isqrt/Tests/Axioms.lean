module

meta import Isqrt.Proofs.IterativeCorrectness
meta import Isqrt.Proofs.RecursiveCorrectness

/-!
The axioms the correctness theorems and the definitions they are about rest on, pinned.

`lake build --wfail` already rejects an incomplete proof, since `sorry` emits a warning. It does
not reject an axiom introduced deliberately, and nothing else records what the theorems depend
on, so each one's axiom set is asserted here: `propext`, `Classical.choice` and `Quot.sound` are
Lean's own three, and any addition fails the build.

Each theorem is checked separately rather than relying on one to cover the other transitively,
so that a change to one proof cannot quietly narrow what is checked.

The three definitions are pinned as well, and they are where the sets differ. `isqrtIterative`
needs `propext` alone — it reaches even that only because `ForIn` is derived from `ForIn'`, whose
membership invariant is a propositional equality it never uses. The two recursive definitions add
`Quot.sound` as the price of well-founded recursion, which equation compilation pays whether or
not the recursion is hard to justify. Neither needs `Classical.choice`: the termination proof is
`omega`, and a tactic's proof term is part of the definition, so a tactic that reasons
classically would show up here.
-/

/--
info: 'isqrtIterative' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms isqrtIterative

/--
info: 'nsqrtRecursive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms nsqrtRecursive

/--
info: 'isqrtRecursive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isqrtRecursive

/--
info: 'isCorrectIsqrt_isqrtIterative' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isCorrectIsqrt_isqrtIterative

/--
info: 'isCorrectIsqrt_isqrtRecursive' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isCorrectIsqrt_isqrtRecursive
