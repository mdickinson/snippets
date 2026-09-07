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

A target already within the limit is its own best approximation, and that needs none of the
machinery: `isBestApproximation_self` proves it from the distance being zero.

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
  obtain ⟨hs₁, hl₁, hall₁⟩ := h₁
  obtain ⟨hs₂, hl₂, hall₂⟩ := h₂
  obtain ⟨hclose₁, hden₁, hnum₁⟩ := hall₁ r₂ s₂ hs₂ hl₂
  obtain ⟨hclose₂, hden₂, hnum₂⟩ := hall₂ r₁ s₁ hs₁ hl₁
  have hs : s₁ = s₂ := Int.le_antisymm (hden₁ hclose₂) (hden₂ hclose₁)
  exact ⟨Int.le_antisymm (hnum₁ hclose₂ hs) (hnum₂ hclose₁ hs.symm), hs⟩

/--
The result is in lowest terms, and that is a consequence of the specification rather than a
part of it.

Were `r` and `s` to share a factor `g > 1`, the reduced pair `(r / g, s / g)` would be a
candidate in its own right: its denominator is positive and strictly smaller, so still within
the limit. It is also *exactly* as close to the target, because scaling a pair down by `g`
scales its residual `m * s - r * n` down by `g` too, which cancels against the `s` on the
other side of `atLeastAsClose`. The second clause applied to that candidate would then give
`s ≤ s / g`, which is false. So minimality of the denominator already forces lowest terms.
-/
public theorem isBestApproximation.gcd_eq_one {m n l r s : Int}
    (h : isBestApproximation m n l r s) : Int.gcd r s = 1 := by
  obtain ⟨hs, hsl, hall⟩ := h
  obtain ⟨g, hgdef⟩ : ∃ g : Int, ((Int.gcd r s : Nat) : Int) = g := ⟨_, rfl⟩
  have hgr : g ∣ r := hgdef ▸ Int.gcd_dvd_left r s
  have hgs : g ∣ s := hgdef ▸ Int.gcd_dvd_right r s
  have hne : Int.gcd r s ≠ 0 := by
    intro h0; have := Int.gcd_eq_zero_iff.mp h0; omega
  rcases (by omega : Int.gcd r s = 1 ∨ 2 ≤ Int.gcd r s) with hone | hg2n
  · exact hone
  exfalso
  have hg2 : 2 ≤ g := by omega
  obtain ⟨s', hs'⟩ := hgs
  obtain ⟨r', hr'⟩ := hgr
  have hs'pos : 0 < s' := by
    rcases (by omega : s' ≤ 0 ∨ 0 < s') with hle | hlt
    · have : g * s' ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hle
      omega
    · exact hlt
  have hs'lt : s' < s := by
    have : 2 * s' ≤ g * s' := Int.mul_le_mul_of_nonneg_right hg2 (by omega)
    omega
  have hres : m * s - r * n = g * (m * s' - r' * n) := by rw [hs', hr']; grind
  have hclose : atLeastAsClose m n r' s' r s := by
    unfold atLeastAsClose
    rw [hres, Int.abs_mul_of_pos (by omega : (0 : Int) < g), hs']
    grind
  have := (hall r' s' hs'pos (by omega)).2.1 hclose
  omega

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
  have h1 : 0 ≤ (m * z - y * n).abs * n := Int.mul_nonneg (Int.abs_nonneg _) (by omega)
  have key : atLeastAsClose m n y z m n → y * n = m * z := by
    intro hrev
    unfold atLeastAsClose at hrev
    rw [h0] at hrev
    have h2 : (m * z - y * n).abs = 0 := by
      rcases Int.mul_eq_zero.mp (show (m * z - y * n).abs * n = 0 by omega) with h | h
      · exact h
      · omega
    have := Int.abs_eq_zero.mp h2
    omega
  refine ⟨?_, fun hrev => ?_, fun hrev hnz => ?_⟩
  · unfold atLeastAsClose; rw [h0]; omega
  · exact Int.le_of_mul_eq_mul_of_gcd_eq_one hgcd hz (key hrev)
  · have := Int.eq_of_mul_eq_mul_right (show n ≠ 0 by omega)
      (show y * n = m * n by rw [key hrev, hnz])
    omega

namespace Bracketing

variable {m n l b c r s t u v : Int}

/--
The loop candidate is a best approximation when it is the nearer of the two.

On its own side of the bracket the three clauses read straight off; on the extended candidate's
side, closeness needs the comparison, and matching the distance exactly there forces an exact
tie, which is the one configuration where the two candidates share a denominator.
-/
public theorem isBestApproximation_loop (h : Bracketing m n l b c r s t u v)
    (hnearer : b * u ≤ c * s) : isBestApproximation m n l r s := by
  refine ⟨h.s_pos, h.s_le_l, fun y z hz hzl => ?_⟩
  unfold atLeastAsClose
  rcases h.cases (y := y) (z := z) hz hzl with ⟨hside, hpos⟩ | ⟨hpos, hside⟩
  · obtain ⟨hle, hvanishes⟩ := h.loop_le_of_loop_side hz hside
    refine ⟨hle, fun hrev => ?_, fun hrev hseq => ?_⟩
    · exact (h.s_le_of_loop_vanishes hpos (hvanishes hrev)).1
    · have := (h.s_le_of_loop_vanishes hpos (hvanishes hrev)).2 hseq
      omega
  · obtain ⟨hle, hpins⟩ := h.loop_le_of_extended_side hz hside hnearer
    refine ⟨hle, fun hrev => ?_, fun hrev hseq => ?_⟩
    · obtain ⟨htie, hzero⟩ := hpins hrev
      have := (h.u_le_of_extended_vanishes hpos hzero).1
      have := h.s_le_u_of_tie htie
      omega
    · obtain ⟨htie, hzero⟩ := hpins hrev
      obtain ⟨hule, heq⟩ := h.u_le_of_extended_vanishes hpos hzero
      have hsu := h.s_le_u_of_tie htie
      -- `s = z` squeezes `s = u = z`: both denominators are one, and the loop candidate is the
      -- lower of two consecutive integers.
      have hsu_eq : s = u := by omega
      have hbc : b = c :=
        Int.eq_of_mul_eq_mul_right (show u ≠ 0 by have := h.u_pos; omega) (by rw [htie, hsu_eq])
      have := heq (by omega)
      have := h.t_eq_of_tie hsu_eq hbc
      omega

/--
The extended candidate is a best approximation when it is strictly the nearer of the two.

Strictness is what makes its loop-candidate-side tie-break clauses vacuous: no candidate over
there can be at least as close in both directions.
-/
public theorem isBestApproximation_extended (h : Bracketing m n l b c r s t u v)
    (hnearer : c * s < b * u) : isBestApproximation m n l t u := by
  refine ⟨h.u_pos, h.u_le_l, fun y z hz hzl => ?_⟩
  unfold atLeastAsClose
  rcases h.cases (y := y) (z := z) hz hzl with ⟨hside, _⟩ | ⟨hpos, hside⟩
  · have hlt := h.extended_lt_of_loop_side hz hside hnearer
    exact ⟨by omega, fun hrev => absurd hrev (by omega), fun hrev => absurd hrev (by omega)⟩
  · obtain ⟨hle, hvanishes⟩ := h.extended_le_of_extended_side hz hside
    refine ⟨hle, fun hrev => ?_, fun hrev hueq => ?_⟩
    · exact (h.u_le_of_extended_vanishes hpos (hvanishes hrev)).1
    · have := (h.u_le_of_extended_vanishes hpos (hvanishes hrev)).2 hueq
      omega

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
