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

/-- Unwrapping of descend_n to shift form. -/
private theorem descend_n_shift (p : SizedProblem) (hc : 0 < p.c) :
    let k := (p.n.toNat.size - 3) / 4; (p.descend hc).n = p.n >>> (2 * k + 2) := by
  obtain ⟨hpos, hc_eq⟩ := p.hsize
  grind only [SizedProblem.descend_n, SizedProblem.shifter_eq]

/-- Unwrapping of newtonLift to shift form. -/
private theorem newtonLift_shift (p : SizedProblem) {a : Int} :
    let k := (p.n.toNat.size - 3) / 4
    p.newtonLift a = (a <<< k) + (p.n >>> (k + 2)) / a := by
  obtain ⟨hpos, hc_eq⟩ := p.hsize
  grind only [SizedProblem.newtonLift_eq, SizedProblem.shifter_eq]

/-! ## Base case, Newton lift, correction -/

/-- Base case: at level `p.c = 0` the value `p.n` is below 4, so `1` is a near square root of it. -/
public theorem isNearSquareRoot_one (p : SizedProblem) (hc : p.c = 0) :
    isNearSquareRoot p.n 1 := isqrt_base_case p.n_pos (p.n_lt_four.mp hc)

/-- The Newton refinement step: a near square root of the descended problem lifts to one of `p`. -/
public theorem isNearSquareRoot_newtonLift (p : SizedProblem) (hc : 0 < p.c) {a : Int}
    (h : isNearSquareRoot (p.descend hc).n a) : isNearSquareRoot p.n (p.newtonLift a) :=
  newtonLift_shift p ▸ key_lemma_bitwise (p.four_le_n.mp hc) (descend_n_shift p hc ▸ h)

/-- Turn a near square root into the integer square root: subtract one exactly when `n < a*a`. -/
public theorem isIntegerSquareRoot_of_isNearSquareRoot {n a : Int} (h : isNearSquareRoot n a) :
    isIntegerSquareRoot n (if n < a * a then a - 1 else a) := by
  obtain ⟨ha_pos, h_lo, h_hi⟩ := h
  by_cases h_lt : n < a * a
  · simp only [h_lt, ↓reduceIte]
    exact ⟨by omega, Int.le_of_lt h_lo, by grind only⟩
  · simp only [h_lt, ↓reduceIte]
    exact ⟨Int.le_of_lt ha_pos, Int.not_lt.mp h_lt, h_hi⟩
