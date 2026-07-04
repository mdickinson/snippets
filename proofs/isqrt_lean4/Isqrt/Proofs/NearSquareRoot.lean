/-
The lifting lemma in the algorithm's bit-oriented form, plus the closing correction step — the
near-square-root machinery both top-level correctness proofs share.

`key_isqrt_lemma` (in `Isqrt.Proofs.KeyLemma`) lifts a near square root across a *general* suitable
scaler `M`; the algorithms use the *specific* power-of-two scaler `2^shifter` carried by a
`SizedProblem`. `isNearSquareRoot_newtonLift` specialises the key lemma to that scaler, giving the
concrete lift both proofs run. `isIntegerSquareRoot_of_isNearSquareRoot` is the closing step: a near
square root of `n`, corrected by a single comparison, is the integer square root of `n`.
-/

module

public import Isqrt.Proofs.SizedProblem
import Isqrt.Proofs.KeyLemma

/-! ## Lifting: the key lemma at the algorithm's power-of-two scaler -/

/-- The Newton refinement step: a near square root of the descended problem lifts to one of `p`. -/
public theorem isNearSquareRoot_newtonLift {p : SizedProblem} (hc : 0 < p.c) {a : Int}
    (h : isNearSquareRoot (p.descend hc).n a) : isNearSquareRoot p.n (p.newtonLift a) := by
  have hscaler : isSuitableScaler p.n p.scaler :=
    isSuitableScaler_of_hasSizeCondition rfl hc p.hsc
  rw [p.descend_n_eq hc] at h
  rw [p.newtonLift_eq]
  exact key_isqrt_lemma hscaler h

/-! ## Correction: near square root to integer square root -/

/-- Turn a near square root into the integer square root: subtract one exactly when `n < a*a`. -/
public theorem isIntegerSquareRoot_of_isNearSquareRoot {a n : Int} (h : isNearSquareRoot n a) :
    isIntegerSquareRoot n (if n < a * a then a - 1 else a) := by
  obtain ⟨_, h_lo, h_hi⟩ := h
  by_cases h_lt : n < a * a
  · simp only [h_lt, ↓reduceIte]
    exact ⟨Int.le_of_lt h_lo, by grind only⟩
  · simp only [h_lt, ↓reduceIte]
    exact ⟨Int.not_lt.mp h_lt, h_hi⟩
