module

public import LimitDenominator.Definitions.Specification
public import LimitDenominator.Proofs.TieBreak

/-!
Whichever candidate the final comparison picks satisfies the specification.

This is where the bracket and the tie-breaking meet the two clauses of
`isBestApproximation`. Both theorems below follow the same shape: split the candidate `(y, z)`
by which side of the bracket it lies on, and in each case either read off the bound directly or
transfer it from the other candidate. The two differ only in the tie: `isBestApproximation_loop`
gets the non-strict comparison, because the code returns the loop candidate on a tie, and
`isBestApproximation_extended` gets the strict one, which is what makes its
loop-candidate-side cases impossible.

The bracket states its bounds as target-minus-candidate, the orientation the loop's own
residuals come in; `atLeastAsClose` is candidate-minus-target. Each proof below crosses
between the two by `Int.abs_neg`.

A target already within the limit is its own best approximation, and that needs none of the
machinery: `isBestApproximation_self` proves it from the distance being zero.

Nothing about the monad, the loop or the Python listing appears here; this is the last of the
math.
-/

/--
A target in lowest terms whose denominator is already within the limit is its own best
approximation — the fast path.

Its distance to itself is zero, so the first clause is immediate, and a rival at distance zero
too is the same fraction, whose denominator is therefore a multiple of this one.
-/
public theorem isBestApproximation_self {m n l : Int} (hn : 0 < n) (hl : n ≤ l)
    (hgcd : Int.gcd m n = 1) : isBestApproximation m n l m n := by
  have h0 : (m * n - m * n).abs = 0 := Int.abs_eq_zero.mpr (by omega)
  refine ⟨hn, hl, fun y z hz _ => ?_⟩
  have h1 : 0 ≤ (y * n - m * z).abs * n := Int.mul_nonneg (Int.abs_nonneg _) (by omega)
  have key : atLeastAsClose m n y z m n → y * n = m * z := by
    intro hrev
    unfold atLeastAsClose at hrev
    rw [h0] at hrev
    have h2 : (y * n - m * z).abs = 0 := by
      rcases Int.mul_eq_zero.mp (show (y * n - m * z).abs * n = 0 by omega) with h | h
      · exact h
      · omega
    have := Int.abs_eq_zero.mp h2
    omega
  refine ⟨?_, fun hrev => ?_⟩
  · unfold atLeastAsClose; rw [h0]; omega
  · exact Int.le_of_mul_eq_mul_of_gcd_eq_one hgcd hz (key hrev)

namespace Bracketing

variable {m n l b c r s t u v : Int}

/--
The loop candidate is a best approximation when it is the nearer of the two.

On its own side of the bracket both clauses read straight off; on the extended candidate's
side, closeness needs the comparison, and a rival matching the distance exactly there is
pinned at the extended candidate's denominator or above, which is at least `s`.
-/
public theorem isBestApproximation_loop (h : Bracketing m n l b c r s t u v)
    (hnearer : b * u ≤ c * s) : isBestApproximation m n l r s := by
  refine ⟨h.s_pos, h.s_le_l, fun y z hz hzl => ?_⟩
  unfold atLeastAsClose
  rw [show r * n - m * s = -(m * s - r * n) by omega,
    show y * n - m * z = -(m * z - y * n) by omega, Int.abs_neg, Int.abs_neg]
  rcases h.cases (y := y) (z := z) hz hzl with ⟨hside, hpos⟩ | ⟨hpos, hside⟩
  · obtain ⟨hle, hvanishes⟩ := h.loop_le_of_loop_side hz hside
    exact ⟨hle, fun hrev => (h.s_le_of_loop_vanishes hpos (hvanishes hrev)).1⟩
  · obtain ⟨hle, hpins⟩ := h.loop_le_of_extended_side hz hside hnearer
    refine ⟨hle, fun hrev => ?_⟩
    obtain ⟨htie, hzero⟩ := hpins hrev
    have := (h.u_le_of_extended_vanishes hpos hzero).1
    have := h.s_le_u_of_tie htie
    omega

/--
The extended candidate is a best approximation when it is strictly the nearer of the two.

Strictness is what makes its loop-candidate-side tie-break clause vacuous: no candidate over
there can be at least as close in both directions.
-/
public theorem isBestApproximation_extended (h : Bracketing m n l b c r s t u v)
    (hnearer : c * s < b * u) : isBestApproximation m n l t u := by
  refine ⟨h.u_pos, h.u_le_l, fun y z hz hzl => ?_⟩
  unfold atLeastAsClose
  rw [show t * n - m * u = -(m * u - t * n) by omega,
    show y * n - m * z = -(m * z - y * n) by omega, Int.abs_neg, Int.abs_neg]
  rcases h.cases (y := y) (z := z) hz hzl with ⟨hside, _⟩ | ⟨hpos, hside⟩
  · have hlt := h.extended_lt_of_loop_side hz hside hnearer
    exact ⟨by omega, fun hrev => absurd hrev (by omega)⟩
  · obtain ⟨hle, hvanishes⟩ := h.extended_le_of_extended_side hz hside
    exact ⟨hle, fun hrev => (h.u_le_of_extended_vanishes hpos (hvanishes hrev)).1⟩

/-! ## Against the comparison the code computes -/

/--
The two theorems above against `2 * b * u ≤ n`, the comparison the code computes, so that the
correctness proofs need only split on the `if`; `loop_nearer_iff` identifies the two.
-/
public theorem isBestApproximation_loop_of_test (h : Bracketing m n l b c r s t u v)
    (htest : 2 * b * u ≤ n) : isBestApproximation m n l r s :=
  h.isBestApproximation_loop (h.loop_nearer_iff.mp htest)

/-- The other arm of the same `if`, where the comparison comes out strict. -/
public theorem isBestApproximation_extended_of_test (h : Bracketing m n l b c r s t u v)
    (htest : ¬2 * b * u ≤ n) : isBestApproximation m n l t u :=
  h.isBestApproximation_extended (by have := h.loop_nearer_iff; omega)

end Bracketing
