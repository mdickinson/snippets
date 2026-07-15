/-
The near-square-root steps both correctness proofs assemble: the base case `isNearSquareRoot_one`
(level zero ⇒ `1`), the Newton step `isNearSquareRoot_newtonLift`, and the closing correction
`isIntegerSquareRoot_of_isNearSquareRoot`. The step recasts the shift-form `descend`/`newtonLift`
into the multiplicative form the general key lemma reads.
-/

module

public import Isqrt.Definitions.Specification
public import Isqrt.Proofs.SizedProblem
import Isqrt.Proofs.KeyLemmaBitwise

/-! ## Base case, Newton lift, correction -/

/-- Base case: at level `p.c = 0` the value `p.n` is below 4, so `1` is a near square root of it. -/
public theorem isNearSquareRoot_one (p : SizedProblem) (hp : p.irreducible) :
    isNearSquareRoot p.n 1 :=
  isqrt_base_case p.n_pos (p.n_lt_four.mp hp)

/-- The Newton refinement step: a near square root of the descended problem lifts to one of `p`. -/
public theorem isNearSquareRoot_newtonLift (p : SizedProblem) (hp : p.reducible) {a : Int}
    (h : isNearSquareRoot (p.descend hp).n a) :
    isNearSquareRoot p.n (p.newtonLift a) := by
  rw [SizedProblem.newtonLift_eq, SizedProblem.k_eq]
  apply key_lemma_bitwise (p.four_le_n.mp hp)
  rw [← SizedProblem.k_eq, ← p.descend_n]
  exact h

/-- Turn a near square root into the integer square root: subtract one exactly when `n < a*a`. -/
public theorem isIntegerSquareRoot_of_isNearSquareRoot {n a : Int} (h : isNearSquareRoot n a) :
    isIntegerSquareRoot n (if n < a * a then a - 1 else a) := by
  obtain ⟨ha_pos, h_lo, h_hi⟩ := h
  by_cases h_lt : n < a * a
  · simp only [h_lt, ↓reduceIte]
    exact ⟨by omega, Int.le_of_lt h_lo, by grind only⟩
  · simp only [h_lt, ↓reduceIte]
    exact ⟨Int.le_of_lt ha_pos, Int.not_lt.mp h_lt, h_hi⟩
