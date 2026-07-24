module

public import Isqrt.Proofs.KeyLemmaBitwise
public import Isqrt.Proofs.NatSize
public import Isqrt.Proofs.SupportLemmas

/-!
The `SizedProblem` structure — a positive value `n`, with recursion level `c` and step shift `k`
derived from its bit length — and the shift-form operations `descend` / `newtonLift` both
correctness proofs build on.
-/

/-! ## The sized problem -/

/-- A *sized problem*: a positive value `n` whose near square root is sought. -/
public structure SizedProblem where
  /-- The value whose near square root is sought (at this recursion level). -/
  n : Int
  n_pos : 0 < n

namespace SizedProblem

-- The operations below are intentionally unexposed, so clients go through the equation lemmas
-- rather than unfolding shift arithmetic. Those lemmas are proved with `(rfl)`, not `rfl`, to stay
-- propositional — bare `rfl` would force the operations to be exposed. See
-- https://github.com/leanprover/lean4/issues/12803.

/-- Constructor for `SizedProblem`. -/
public def ofPos {n : Int} (hn : 0 < n) : SizedProblem := ⟨n, hn⟩

/-- A problem `p` is *reducible* if `p.n ≥ 4`. -/
public def reducible (p : SizedProblem) : Prop := 4 ≤ p.n

/-- ... and *irreducible* if it's not reducible. -/
public abbrev irreducible (p : SizedProblem) : Prop := ¬p.reducible

/--
`p.c` is the size of `p.n` in base 4: the floor of `log_4 n`, or one less than the
number of digits of `n` when it's written in base 4.
-/
public def c (p : SizedProblem) : Nat := (p.n.toNat.size - 1) / 2

/-- `p.k` is the base value used for shifts when descending `p`. -/
public def k (p : SizedProblem) : Nat := (p.n.toNat.size - 3) / 4

/-- The problem is reducible if and only if 0 < p.c. -/
public theorem reducible_iff {p : SizedProblem} : p.reducible ↔ 0 < p.c := by
  rw [reducible, c, show (4 : Int) = 2^2 by decide, ← Int.lt_size]
  omega

/-- Counterpart for irreducibility. -/
public theorem irreducible_iff {p : SizedProblem} : p.irreducible ↔ p.c = 0 := by
  grind only [reducible_iff]

theorem descended_n_pos (p : SizedProblem) (hp : p.reducible) :
    0 < _root_.descend p.n p.k := by
  have : 2 < p.n.toNat.size := Int.lt_size.mpr hp
  apply Int.shiftRight_pos
  grind only [k]

/-- For a reducible SizedProblem, descend gives its reduction. -/
public def descend {p : SizedProblem} (hp : p.reducible) : SizedProblem :=
  SizedProblem.ofPos (n := _root_.descend p.n p.k) (descended_n_pos p hp)

/-- And newtonLift lifts a near square root for the descended problem back -/
public def newtonLift (p : SizedProblem) (a : Int) : Int := _root_.newtonLift p.n p.k a

/-- The problem is reducible if and only if n is at least 4. -/
theorem four_le_n (p : SizedProblem) : p.reducible ↔ 4 ≤ p.n := by rfl

/-- The problem is irreducible if and only if n is less than 4. -/
theorem n_lt_four (p : SizedProblem) : p.irreducible ↔ p.n < 4 := by
  grind only [four_le_n]

/-- The seed problem's value is `n`. -/
public theorem ofPos_n {n : Int} (hn : 0 < n) : (ofPos hn).n = n := (rfl)

/-- Two `SizedProblem`s are equal if their `n`s are equal. -/
public theorem eq_of_n_eq {p q : SizedProblem} : p.n = q.n → p = q := (mk.injEq _ _ _ _).mpr

/-- The descended level is `⌊c/2⌋`. -/
public theorem descend_c (p : SizedProblem) (hp : p.reducible) : (p.descend hp).c = p.c / 2 := by
  grind only [descend, ofPos_n, Int.size_shiftRight, c, k]

/-- Descending strictly lowers the size of `n`, so the recursion terminates. -/
public theorem descend_lt (p : SizedProblem) (hp : p.reducible) :
    (p.descend hp).n.toNat.size < p.n.toNat.size := by
  have : 0 < p.n.toNat.size := Int.lt_size.mpr ((Int.pow_zero 2) ▸ p.n_pos)
  grind only [descend, ofPos_n, Int.size_shiftRight]

/-- `k` in terms of `c`. -/
public theorem k_of_c (p : SizedProblem) : p.k = (p.c - 1) / 2 := by rw [c, k]; omega

/-- Expose the definitions of `c`, `k`, `descend` and `newtonLift`. -/
public theorem c_eq (p : SizedProblem) : p.c = (p.n.toNat.size - 1) / 2 := (rfl)

theorem k_eq (p : SizedProblem) : p.k = (p.n.toNat.size - 3) / 4 := (rfl)

public theorem descend_n (p : SizedProblem) (hp : p.reducible) :
    (p.descend hp).n = _root_.descend p.n p.k := (rfl)

public theorem newtonLift_eq (p : SizedProblem) (a : Int) :
    p.newtonLift a = _root_.newtonLift p.n p.k a := (rfl)

/-- Base case: at level `p.c = 0` the value `p.n` is below 4, so `1` is a near square root of it. -/
public theorem nsqrt_base {p : SizedProblem} (hp : p.irreducible) :
    isNearSquareRoot p.n 1 :=
  _root_.nsqrt_base p.n_pos (p.n_lt_four.mp hp)

/-- The Newton refinement step: a near square root of the descended problem lifts to one of `p`. -/
public theorem nsqrt_lift {p : SizedProblem} (hp : p.reducible) {a : Int}
    (h : isNearSquareRoot (p.descend hp).n a) :
    isNearSquareRoot p.n (p.newtonLift a) := by
  rw [newtonLift_eq, k_eq]
  apply _root_.nsqrt_lift (p.four_le_n.mp hp)
  rw [← k_eq, ← p.descend_n]
  exact h

end SizedProblem
