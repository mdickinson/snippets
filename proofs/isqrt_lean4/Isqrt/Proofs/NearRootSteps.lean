/-
The closing correction both correctness proofs share: `isIntegerSquareRoot_of_isNearSquareRoot`
turns a near square root of `n` into `⌊√n⌋`, subtracting one exactly when `n < a*a`.
-/

module

public import Isqrt.Definitions.Specification

/-- Turn a near square root into the integer square root: subtract one exactly when `n < a*a`. -/
public theorem isIntegerSquareRoot_of_isNearSquareRoot {n a : Int} (h : isNearSquareRoot n a) :
    isIntegerSquareRoot n (if n < a * a then a - 1 else a) := by
  obtain ⟨ha_pos, h_lo, h_hi⟩ := h
  by_cases h_lt : n < a * a
  · simp only [h_lt, ↓reduceIte]
    exact ⟨by omega, Int.le_of_lt h_lo, by grind only⟩
  · simp only [h_lt, ↓reduceIte]
    exact ⟨Int.le_of_lt ha_pos, Int.not_lt.mp h_lt, h_hi⟩
