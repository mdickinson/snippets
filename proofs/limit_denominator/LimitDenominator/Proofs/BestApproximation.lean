module

public import LimitDenominator.Proofs.TieBreak

/-!
Whichever candidate the final comparison picks satisfies the specification.

This is where the bracket and the tie-breaking meet the three clauses of
`isBestApproximation`. Both theorems below follow the same shape: split the candidate `(y, z)`
by which side of the bracket it lies on, and in each case either read off the bound directly or
transfer it from the other candidate. The two differ only in the tie: `isBestApproximation_loop`
gets the non-strict comparison, because the code returns the loop candidate on a tie, and
`isBestApproximation_extended` gets the strict one, which is what makes its
loop-candidate-side cases impossible.

Nothing about the monad, the loop or the Python listing appears here; this is the last of the
math.
-/

/--
The specification determines the result: at most one pair satisfies it.

Each of two best approximations is at least as close as the other, so the second clause makes
their denominators equal and the third then makes their numerators equal. This is why proving
`isBestApproximation` of the returned pair is enough — the specification cannot be met by some
unintended pair as well.
-/
public theorem isBestApproximation_unique {m n l r₁ s₁ r₂ s₂ : Int}
    (h₁ : isBestApproximation m n l r₁ s₁) (h₂ : isBestApproximation m n l r₂ s₂) :
    r₁ = r₂ ∧ s₁ = s₂ := by
  obtain ⟨hs₁, hl₁, -, hall₁⟩ := h₁
  obtain ⟨hs₂, hl₂, -, hall₂⟩ := h₂
  obtain ⟨hclose₁, hden₁, hnum₁⟩ := hall₁ r₂ s₂ hs₂ hl₂
  obtain ⟨hclose₂, hden₂, hnum₂⟩ := hall₂ r₁ s₁ hs₁ hl₁
  have hs : s₁ = s₂ := Int.le_antisymm (hden₁ hclose₂) (hden₂ hclose₁)
  exact ⟨Int.le_antisymm (hnum₁ hclose₂ hs) (hnum₂ hclose₁ hs.symm), hs⟩

namespace Bracketing

variable {m n l b c r s t u : Int}

/-- The loop candidate is a best approximation when it is the nearer of the two. -/
public theorem isBestApproximation_loop (h : Bracketing m n l b c r s t u)
    (hnearer : b * u ≤ c * s) : isBestApproximation m n l r s := by
  refine ⟨h.s_pos, h.s_le_l, h.gcd_loop, fun y z hz hzl => ?_⟩
  have habs := h.abs_loop
  have hside := h.outside (y := y) (z := z) hzl
  -- The closeness clause: read off on the loop candidate's side, transferred on the other.
  have hclose : b * z ≤ (m * z - y * n).abs * s := by
    rcases hside with hloop | hextended
    · exact h.loop_le_of_side hloop
    · exact h.loop_le_of_extended_le hnearer hz (h.extended_le_of_side hextended)
  -- Both tie-break clauses, from a candidate that is at least as close.
  have key : (m * z - y * n).abs * s ≤ b * z → s ≤ z ∧ (s = z → r ≤ y) := by
    intro hrev
    have hmatch : b * z = (m * z - y * n).abs * s := by omega
    rcases hside with hloop | hextended
    · -- The candidate equals the loop candidate as a value, so its denominator is a multiple.
      have hval : y * s = r * z := h.eq_of_loop_le hloop hrev
      refine ⟨Int.le_of_mul_eq_mul_of_gcd_eq_one h.gcd_loop hz hval, fun hseq => ?_⟩
      have hys : y * s = r * s := by rw [hval, ← hseq]
      have := Int.eq_of_mul_eq_mul_right (show s ≠ 0 by have := h.s_pos; omega) hys
      omega
    · -- Matching the loop candidate's distance from beyond the extended candidate is a tie.
      have htie : b * u = c * s :=
        Int.le_antisymm hnearer
          (h.extended_nearer_of_match hz (h.extended_le_of_side hextended) hmatch)
      have hmatch' : c * z = (m * z - y * n).abs * u := h.extended_match_of_tie htie hmatch
      have hval : t * z = y * u := h.eq_of_extended_le hextended (by omega)
      have huz : u ≤ z :=
        Int.le_of_mul_eq_mul_of_gcd_eq_one (y := y) h.gcd_extended hz (by omega)
      refine ⟨by have := h.s_le_u_of_tie htie; omega, fun hseq => ?_⟩
      -- `s = z` squeezes `s = u = z`, so the two candidates coincide in the tie configuration
      -- where both denominators are one and the loop candidate is the lower bound.
      have hsu : s = u := by have := h.s_le_u_of_tie htie; omega
      have hbc : b = c :=
        Int.eq_of_mul_eq_mul_right (show u ≠ 0 by have := h.u_pos; omega) (by rw [htie, hsu])
      have hdet := h.det_eq_one_of_tie hsu hbc
      have hty : t = y :=
        Int.eq_of_mul_eq_mul_right (show u ≠ 0 by have := h.u_pos; omega)
          (show t * u = y * u by grind)
      rcases (by omega : t - r ≤ 0 ∨ 1 ≤ t - r) with hle | hge
      · have hnonpos : s * (t - r) ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos (by have := h.s_pos; omega) hle
        grind
      · omega
  refine ⟨?_, fun hrev => ?_, fun hrev hseq => ?_⟩
  · unfold atLeastAsClose; rw [habs]; exact hclose
  · unfold atLeastAsClose at hrev; rw [habs] at hrev; exact (key hrev).1
  · unfold atLeastAsClose at hrev; rw [habs] at hrev; exact (key hrev).2 hseq

/-- The extended candidate is a best approximation when it is strictly the nearer of the two. -/
public theorem isBestApproximation_extended (h : Bracketing m n l b c r s t u)
    (hnearer : c * s < b * u) : isBestApproximation m n l t u := by
  refine ⟨h.u_pos, h.u_le_l, h.gcd_extended, fun y z hz hzl => ?_⟩
  have habs := h.abs_extended
  have hside := h.outside (y := y) (z := z) hzl
  have hclose : c * z ≤ (m * z - y * n).abs * u := by
    rcases hside with hloop | hextended
    · exact h.extended_le_of_loop_le (by omega) hz (h.loop_le_of_side hloop)
    · exact h.extended_le_of_side hextended
  have key : (m * z - y * n).abs * u ≤ c * z → u ≤ z ∧ (u = z → t ≤ y) := by
    intro hrev
    have hmatch : c * z = (m * z - y * n).abs * u := by omega
    rcases hside with hloop | hextended
    · -- Impossible: a candidate beyond the loop candidate that matches the extended candidate's
      -- distance would make the loop candidate the nearer.
      exact absurd (h.loop_nearer_of_match hz (h.loop_le_of_side hloop) hmatch) (by omega)
    · have hval : t * z = y * u := h.eq_of_extended_le hextended hrev
      refine ⟨Int.le_of_mul_eq_mul_of_gcd_eq_one (y := y) h.gcd_extended hz (by omega),
        fun hueq => ?_⟩
      have hty : t = y :=
        Int.eq_of_mul_eq_mul_right (show u ≠ 0 by have := h.u_pos; omega)
          (show t * u = y * u by grind)
      omega
  refine ⟨?_, fun hrev => ?_, fun hrev hueq => ?_⟩
  · unfold atLeastAsClose; rw [habs]; exact hclose
  · unfold atLeastAsClose at hrev; rw [habs] at hrev; exact (key hrev).1
  · unfold atLeastAsClose at hrev; rw [habs] at hrev; exact (key hrev).2 hueq

end Bracketing
