module

public import Isqrt.Proofs.SizedProblem

/-!
The subproblem chain that feeds into the iterative proof.
-/

/-- The iteration-`i` subproblem descending from `p`: value `p.n >>> 2(c - c>>>i)` at level
`c >>> i`. -/
public def subAt (p : SizedProblem) (i : Nat) : SizedProblem :=
  SizedProblem.ofPos (
    show 0 < p.n >>> (2 * (p.c - (p.c >>> i)))
    from Int.shiftRight_pos (by grind only [p.c_eq, Int.size_pos.mpr p.n_pos])
  )

/-- The *height* of a problem: `subAt p i` makes sense for `i ≤ p.height`. -/
@[expose]
public def SizedProblem.height (p : SizedProblem) : Nat := p.c.size

/-- The iteration-`i` subproblem's value in shift form. -/
public theorem subAt_n (p : SizedProblem) (i : Nat) :
    (subAt p i).n = p.n >>> (2 * (p.c - p.c >>> i)) := by
  unfold subAt; rw [SizedProblem.ofPos_n]

/-- The iteration-`i` subproblem's level is `c >>> i`. -/
public theorem subAt_c (p : SizedProblem) (i : Nat) : (subAt p i).c = p.c >>> i := by
  grind only [subAt, SizedProblem.ofPos_n, SizedProblem.c_eq, Int.size_shiftRight,
    Nat.shiftRight_le]

/-- The iteration-`i` subproblem's `k` is `((c >>> i) - 1)/2`. -/
public theorem subAt_k (p : SizedProblem) (i : Nat) : (subAt p i).k = (p.c >>> i - 1) / 2 := by
  rw [SizedProblem.k_of_c, subAt_c]

/-- Chain top: iteration `0` is the whole problem. -/
theorem subAt_zero (p : SizedProblem) : subAt p 0 = p := by
  apply SizedProblem.eq_of_n_eq
  simp only [subAt, SizedProblem.ofPos_n, Nat.shiftRight_zero, Nat.sub_self, Nat.mul_zero,
    Int.shiftRight_zero]

/-- The subproblem at depth `p.height` is irreducible. -/
theorem subAt_irreducible {p : SizedProblem} : (subAt p p.height).irreducible := by
  rw [SizedProblem.irreducible_iff, subAt_c]
  exact Nat.shiftRight_size_self

/-- Subproblems below depth `p.height` are reducible. -/
theorem subAt_reducible {p : SizedProblem} {i : Nat} (hi : i < p.height) :
    (subAt p i).reducible := by
  rw [SizedProblem.reducible_iff, subAt_c]; exact Nat.shiftRight_pos hi

/-- Chain step: descending iteration `i` gives iteration `i+1`. -/
theorem subAt_descend {p : SizedProblem} {i : Nat} (hp : (subAt p i).reducible) :
    (subAt p i).descend hp = subAt p (i + 1) := by
  apply SizedProblem.eq_of_n_eq
  rw [SizedProblem.descend_n, descend, subAt_n, subAt_n, subAt_k]
  rw [← Int.shiftRight_add, Nat.shiftRight_succ]
  congr 1
  have : p.c >>> i ≤ p.c := by apply Nat.shiftRight_le
  have : 0 < p.c >>> i := subAt_c p i ▸ SizedProblem.reducible_iff.mp hp
  omega

/-- `1` is a near square root of the bottommost subproblem, `subAt p p.height`. -/
public theorem subAt_nsqrt_base (p : SizedProblem) :
    isNearSquareRoot (subAt p p.height).n 1 :=
  SizedProblem.nsqrt_base subAt_irreducible

/-- A near square root of `subAt p (i + 1)` lifts to one of `subAt p i`. -/
public theorem subAt_nsqrt_lift {p : SizedProblem} {i : Nat} (hi : i < p.height)
    {a : Int} (ha : isNearSquareRoot (subAt p (i + 1)).n a) :
    isNearSquareRoot (subAt p i).n ((subAt p i).newtonLift a) :=
  SizedProblem.nsqrt_lift (subAt_reducible hi) (subAt_descend (subAt_reducible hi) ▸ ha)

/-- A near square root of `subAt p 0` is one of `p` itself. -/
public theorem nsqrt_of_subAt_zero {p : SizedProblem} {a : Int}
    (ha : isNearSquareRoot (subAt p 0).n a) : isNearSquareRoot p.n a := by
  rw [subAt_zero] at ha
  exact ha
