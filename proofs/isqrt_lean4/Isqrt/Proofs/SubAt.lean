/-
The subproblem chain that feeds into the iterative proof.
-/

module

public import Isqrt.Proofs.SizedProblem

/-- The subproblem at iteration `i` is well-defined. -/
theorem subAt_pos (p : SizedProblem) (i : Nat) : 0 < p.n >>> (2 * (p.c - (p.c >>> i))) := by
  apply Int.shiftRight_pos
  have : 2 * (p.c - p.c >>> i) ≤ 2 * p.c := by grind only
  apply Nat.lt_of_le_of_lt this
  rw [p.c_eq]
  have : 0 < p.n.toNat.size := by
    rw [Nat.size_pos]
    have := p.n_pos
    omega
  omega

/-- The iteration-`i` subproblem descending from `p`: value `p.n >>> 2(c - c>>>i)` at level
`c >>> i`, carrying the inherited size invariant. -/
public def subAt (p : SizedProblem) (i : Nat) : SizedProblem :=
  SizedProblem.ofPos (subAt_pos p i)

/-- The iteration-`i` subproblem's value in shift form. -/
public theorem subAt_n (p : SizedProblem) (i : Nat) :
    (subAt p i).n = p.n >>> (2 * (p.c - p.c >>> i)) := by
  unfold subAt; rw [SizedProblem.ofPos_n]

/-- The iteration-`i` subproblem's level is `c >>> i`. -/
public theorem subAt_c (p : SizedProblem) (i : Nat) : (subAt p i).c = p.c >>> i := by
  grind only [subAt, SizedProblem.ofPos_n, SizedProblem.c_eq, Int.size_shiftRight, Nat.shiftRight_le]

/-- The iteration-`i` subproblem's `k` is `((c >>> i) - 1)/2`. -/
public theorem subAt_k (p : SizedProblem) (i : Nat) : (subAt p i).k = (p.c >>> i - 1) / 2 := by
  rw [SizedProblem.k_of_c, subAt_c]

/-- Chain top: iteration `0` is the whole problem. -/
public theorem subAt_zero (p : SizedProblem) : subAt p 0 = p := by
  apply SizedProblem.eq_of_n_eq
  simp only [subAt, SizedProblem.ofPos_n, Nat.shiftRight_zero, Nat.sub_self, Nat.mul_zero, Int.shiftRight_zero]

/-- The subproblem at depth `c.size` is irreducible. -/
public theorem subAt_irreducible {p : SizedProblem} : (subAt p p.c.size).irreducible := by
  rw [SizedProblem.irreducible_iff, subAt_c]
  exact Nat.shiftRight_size_self

/-- Subproblems below depth `c.size` are reducible. -/
public theorem subAt_reducible (p : SizedProblem) (i : Nat) (hi : i < p.c.size) :
    (subAt p i).reducible := by
  rw [SizedProblem.reducible_iff, subAt_c]; exact Nat.shiftRight_pos hi

/-- `descend`'s value in terms of the level `c`: it shifts `n` right by `2(c − ⌊c/2⌋)`, the form the
subproblem chain descends by (equivalently `descend_n`'s `2k+2`). -/
theorem descend_n_of_c (p : SizedProblem) (hp : p.reducible) :
    (p.descend hp).n = p.n >>> (2 * (p.c - p.c / 2)) := by
  rw [SizedProblem.descend_n, SizedProblem.c_eq, SizedProblem.k_eq]
  have : 2 < p.n.toNat.size := Int.lt_size.mpr (p.four_le_n.mp hp)
  congr 1; omega

/-- Chain step: descending iteration `i` gives iteration `i+1`. -/
public theorem descend_subAt {p : SizedProblem} {i : Nat} (hp : (subAt p i).reducible) :
    (subAt p i).descend hp = subAt p (i + 1) := by
  apply SizedProblem.eq_of_n_eq
  rw [descend_n_of_c]
  rw [subAt_c, subAt_n, subAt_n]
  rw [← Int.shiftRight_add, ← Nat.shiftRight_succ]
  congr 1
  have : p.c >>> i ≤ p.c := by apply Nat.shiftRight_le
  have : p.c >>> (i + 1) ≤ p.c >>> i := by rw [Nat.shiftRight_add]; apply Nat.shiftRight_le
  omega
