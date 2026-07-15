/-
The bit-length invariant `isSizedAt n c` (`0 < n ∧ c = (n.toNat.size - 1)/2`) and its descent, and
the `SizedProblem` structure carrying it, with the shift-form operations `descend` / `newtonLift`
both correctness proofs build on.
-/

module

public import Isqrt.Proofs.NatSize
public import Isqrt.Proofs.SupportLemmas
import Isqrt.Proofs.PythonTranslation

public section

/-! ## The sized problem -/

/-- A *sized problem*: a value `n`, a recursion level `c`, and the size invariant `isSizedAt n c`
relating them. -/
structure SizedProblem where
  /-- The value whose near square root is sought (at this recursion level). -/
  n : Int
  n_pos : 0 < n

namespace SizedProblem

-- The operations below are intentionally unexposed, so clients go through the equation lemmas
-- rather than unfolding shift arithmetic. Those lemmas are proved with `(rfl)`, not `rfl`, to stay
-- propositional — bare `rfl` would force the operations to be exposed. See
-- https://github.com/leanprover/lean4/issues/12803.

/-- Constructor for `SizedProblem`. -/
def ofPos {n : Int} (hn : 0 < n) : SizedProblem := ⟨n, hn⟩

/-- A problem `p` is *reducible* if `p.n ≥ 4`. -/
def reducible (p : SizedProblem) : Prop := 4 ≤ p.n

/-- ... and *irreducible* if it's not reducible. -/
abbrev irreducible (p : SizedProblem) : Prop := ¬p.reducible

/--
`p.c` is the size of `p.n` in base 4: the floor of `log_4 n`, or one less than the
number of digits of `n` when it's written in base 4.
-/
def c (p : SizedProblem) : Nat := (p.n.toNat.size - 1) / 2

/-- `p.k` is the base value used for shifts when descending `p`. -/
def k (p : SizedProblem) : Nat := (p.n.toNat.size - 3) / 4

/-- The problem is reducible if and only if 0 < p.c. -/
theorem reducible_iff {p : SizedProblem} : p.reducible ↔ 0 < p.c := by
  rw [reducible, c, show (4 : Int) = 2^2 by decide, ← Int.lt_size]
  omega

private theorem descended_n_pos (p : SizedProblem) (hp : p.reducible) :
    0 < p.n >>> (2 * p.k + 2) := by
  have : 2 < p.n.toNat.size := Int.lt_size.mpr hp
  apply Int.shiftRight_pos
  grind only [k]

/-- For a reducible SizedProblem, descend gives its reduction. -/
def descend {p : SizedProblem} (hp : p.reducible) : SizedProblem :=
  SizedProblem.ofPos (n := p.n >>> (2 * p.k + 2)) (descended_n_pos p hp)

/-- And newtonLift lifts a near square root for the descended problem back -/
def newtonLift (p : SizedProblem) (a : Int) : Int :=
  (a <<< p.k) + (p.n >>> (p.k + 2)) / a

/-- Counterpart for irreducibility. -/
theorem irreducible_iff {p : SizedProblem} : p.irreducible ↔ p.c = 0 := by
  grind only [reducible_iff]

/-- The problem is reducible if and only if n is at least 4. -/
theorem four_le_n (p : SizedProblem) : p.reducible ↔ 4 ≤ p.n := by rfl

/-- The problem is irreducible if and only if n is less than 4. -/
theorem n_lt_four (p : SizedProblem) : p.irreducible ↔ p.n < 4 := by
  grind only [four_le_n]

/-- The seed problem's value is `n`. -/
theorem ofPos_n {n : Int} (hn : 0 < n) : (ofPos hn).n = n := (rfl)

/-- The seed problem's level is `(n.toNat.size - 1)/2`. -/
theorem ofPos_c {n : Int} (hn : 0 < n) : (ofPos hn).c = (n.toNat.size - 1) / 2 := (rfl)

/-- Two SizedProblems are equal if and only if their `n`s are equal. -/
theorem eq_of_n_eq {p q : SizedProblem} : p.n = q.n → p = q := (mk.injEq _ _ _ _).mpr

/-- The descended level is `⌊c/2⌋`. -/
theorem descend_c (p : SizedProblem) (hp : p.reducible) : (p.descend hp).c = p.c / 2 := by
  grind only [descend, ofPos_c, Int.size_shiftRight, c, k]

/-- Descending strictly lowers the size of `n`, so the recursion terminates. -/
theorem descend_lt (p : SizedProblem) (hp : p.reducible):
    (p.descend hp).n.toNat.size < p.n.toNat.size := by
  have : 0 < p.n.toNat.size := Int.lt_size.mpr ((Int.pow_zero 2) ▸ p.n_pos)
  grind only [descend, ofPos_n, Int.size_shiftRight]

/-- k in terms of c. -/
theorem k_of_c (p : SizedProblem): p.k = (p.c - 1) / 2 := by rw [c, k]; omega

/-- Expose the definitions of `c`, `k`, `descend` and `newtonLift`. -/
theorem c_eq (p : SizedProblem) : p.c = (p.n.toNat.size - 1) / 2 := (rfl)

theorem k_eq (p : SizedProblem) : p.k = (p.n.toNat.size - 3) / 4 := (rfl)

theorem descend_n (p : SizedProblem) (hp : p.reducible) :
    (p.descend hp).n = p.n >>> (2 * p.k + 2) := (rfl)

theorem newtonLift_eq (p : SizedProblem) (a : Int) :
    p.newtonLift a = (a <<< p.k) + (p.n >>> (p.k + 2)) / a := by (rfl)

end SizedProblem

end
