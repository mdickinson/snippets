module

public import LimitDenominator.Proofs.LoopInvariant

/-!
What holds after loop exit, transcribing the informal proof's § "Details: after the loop".

`Bracketing` collects the facts about the two candidates that the rest of the proof rests on.
Nothing below this file mentions the loop, its state, or `p` and `q`: the bracket argument and
the tie-breaking both read off `Bracketing` alone.
-/

/--
The facts about the loop candidate `r / s` and the extended candidate `t / u` on which the
final comparison rests.

`t * s - r * u` is the orientation: a unit whose sign says which of the two candidates lies
above the target. The two residuals are the scaled distances from the target to each candidate,
oriented so as to be nonnegative — which is what makes the absolute values in the
specification collapse.
-/
public structure Bracketing (m n l b c r s t u : Int) : Prop where
  /-- The two candidates have unit determinant. -/
  det : t * s - r * u = 1 ∨ t * s - r * u = -1
  /-- Oriented scaled distance from the target to the loop candidate. -/
  loop_residual : (m * s - r * n) * (t * s - r * u) = b
  /-- Oriented scaled distance from the target to the extended candidate. -/
  extended_residual : (t * n - m * u) * (t * s - r * u) = c
  /-- The two distances make up the target's denominator. -/
  denominator : c * s + b * u = n
  n_pos : 0 < n
  b_nonneg : 0 ≤ b
  c_pos : 0 < c
  b_le_c : b ≤ c
  s_pos : 0 < s
  s_le_l : s ≤ l
  u_pos : 0 < u
  u_le_l : u ≤ l
  /-- Between them the two denominators exceed the limit: this is what closes the bracket. -/
  l_lt_add : l < s + u
  /--
  The orientation is positive in the single degenerate configuration where both candidates
  have the same denominator and are equidistant from the target. This is the one place the
  proof needs to know that the loop candidate is the *lower* bound rather than the upper one,
  and it descends from `LoopInvariant.p_eq_one_of_q_eq_zero`.
  -/
  det_eq_one_of_tie : s = u → b = c → t * s - r * u = 1

namespace LoopInvariant

/--
The after-loop facts, for a state satisfying the invariant with the loop condition false.

Following the informal proof, `k = ⌊(l - q)/s⌋` advances the previous loop candidate `(p, q)`
as far towards the loop candidate as the denominator limit allows, giving the extended
candidate `(t, u) = (p + kr, q + ks)`; and `c = a - kb` is its oriented distance to the target.
-/
public theorem bracketing {m n l a b c k p q r s t u : Int}
    (h : LoopInvariant m n l a b p q r s)
    (hexit : b = 0 ∨ (0 < b ∧ l < q + a / b * s))
    (hk : k = (l - q) / s) (ht : t = p + k * r) (hu : u = q + k * s) (hc : c = a - k * b) :
    Bracketing m n l b c r s t u := by
  have hres_num := h.numerator_residual
  have hres_den := h.denominator_residual
  obtain ⟨hdet, hnum, hden, hb, hba, hq, hqs, hsl, hs, hp⟩ := h
  -- The defining inequalities for the floor `k`, and the sign facts they need.
  have hk_nonneg : 0 ≤ k := hk ▸ (Int.le_ediv_iff_mul_le hs).mpr (by omega)
  have hk_le : k * s ≤ l - q := (Int.le_ediv_iff_mul_le hs).mp (by omega)
  have hk_lt : l - q < k * s + s := by
    have hfloor := Int.lt_ediv_add_one_mul_self (l - q) hs
    have : ((l - q) / s + 1) * s = k * s + s := by grind
    omega
  have hks_nonneg : 0 ≤ k * s := Int.mul_nonneg hk_nonneg (by omega)
  -- Extending does not change the orientation.
  have horient : t * s - r * u = p * s - r * q := by grind
  -- `b ≤ c` and `0 < c`, by cases on how the loop exited.
  have hbc : b ≤ c ∧ 0 < c := by
    rcases hexit with rfl | ⟨hb_pos, hcond⟩
    · rw [Int.mul_zero, Int.sub_zero] at hc; omega
    · have hk_lt_quot : k < a / b := hk ▸ (Int.ediv_lt_iff_lt_mul hs).mpr (by omega)
      have h1 : (k + 1) * b ≤ a / b * b := Int.mul_le_mul_of_nonneg_right (by omega) hb
      have h2 : a / b * b ≤ a := (Int.le_ediv_iff_mul_le hb_pos).mp (Int.le_refl (a / b))
      have h3 : (k + 1) * b = k * b + b := by grind
      omega
  exact {
    det := horient ▸ hdet
    loop_residual := by rw [horient]; exact hres_den
    extended_residual := by rw [horient]; grind
    denominator := by grind
    n_pos := by
      have := Int.mul_pos (show (0 : Int) < a by omega) hs
      have := Int.mul_nonneg hb hq
      omega
    b_nonneg := hb
    c_pos := hbc.2
    b_le_c := hbc.1
    s_pos := hs
    s_le_l := hsl
    u_pos := by omega
    u_le_l := by omega
    l_lt_add := by omega
    det_eq_one_of_tie := by
      intro htie hbc_eq
      rw [horient]
      -- A tie with equal denominators forces `(k + 1) * b = a`, hence `0 < b` and `1 ≤ k`.
      have hb_pos : 0 < b := by
        rcases (by omega : b = 0 ∨ 0 < b) with rfl | hb_pos
        · rw [Int.mul_zero, Int.sub_zero] at hc; omega
        · exact hb_pos
      have hk_one : 1 ≤ k := by
        rcases (by omega : k ≤ 0 ∨ 1 ≤ k) with hk_le_zero | hk_one
        · have h1 : (k + 1) * b ≤ 1 * b := Int.mul_le_mul_of_nonneg_right (by omega) hb
          have h2 : (k + 1) * b = k * b + b := by grind
          omega
        · exact hk_one
      -- Then `s = q + k*s` with `s ≤ k*s` forces `q = 0`, and so `p = 1`.
      have hks : s ≤ k * s := Int.le_mul_of_one_le_left (by omega) hk_one
      have hq_zero : q = 0 := by omega
      -- The orientation is now `p * s = s`, and a positive unit is one.
      rw [hp hq_zero, hq_zero] at hdet ⊢
      omega
  }

end LoopInvariant
