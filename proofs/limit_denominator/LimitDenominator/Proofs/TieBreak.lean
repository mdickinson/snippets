module

public import LimitDenominator.Proofs.Bracket

/-!
Choosing between the two candidates, transcribing the informal proof's two § "Tie-breaking"
sections.

`b * u ≤ c * s` compares the two scaled distances, and `loop_nearer_iff` identifies it with the
`2 * b * u ≤ n` the code actually computes. The rest of the file is what the comparison buys:
closeness against one candidate transfers to the other when that one is the nearer, on an exact
tie the loop candidate has the smaller denominator, and a candidate that matches one candidate's
distance exactly pins the comparison.
-/

namespace Bracketing

variable {m n l b c r s t u e z : Int}

/-! ## Which candidate is nearer -/

/--
The comparison the code performs is exactly the comparison of the two scaled distances. Adding
`b * u` to both sides of `b * u ≤ c * s` and using `c * s + b * u = n` gives `2 * b * u ≤ n`.
-/
public theorem loop_nearer_iff (h : Bracketing m n l b c r s t u) :
    2 * b * u ≤ n ↔ b * u ≤ c * s := by
  have hassoc : 2 * b * u = 2 * (b * u) := by grind
  have := h.denominator
  omega

/-- On an exact tie the loop candidate has the smaller denominator. -/
public theorem s_le_u_of_tie (h : Bracketing m n l b c r s t u) (htie : b * u = c * s) :
    s ≤ u := by
  have h1 : b * u ≤ c * u := Int.mul_le_mul_of_nonneg_right h.b_le_c (by have := h.u_pos; omega)
  exact Int.le_of_mul_le_mul_left (by omega) h.c_pos

/-! ## Transferring closeness to the nearer candidate -/

/--
When the extended candidate is the nearer of the two, a bound against the loop candidate
transfers to it.
-/
public theorem extended_le_of_loop_le (h : Bracketing m n l b c r s t u)
    (hnearer : c * s ≤ b * u) (hz : 0 < z) (hloop : b * z ≤ e * s) : c * z ≤ e * u := by
  have h1 : c * s * z ≤ b * u * z := Int.mul_le_mul_of_nonneg_right hnearer (by omega)
  have h2 : b * z * u ≤ e * s * u :=
    Int.mul_le_mul_of_nonneg_right hloop (by have := h.u_pos; omega)
  have h3 : s * (c * z) ≤ s * (e * u) := by grind
  exact Int.le_of_mul_le_mul_left h3 h.s_pos

/-- Symmetrically, when the loop candidate is the nearer. -/
public theorem loop_le_of_extended_le (h : Bracketing m n l b c r s t u)
    (hnearer : b * u ≤ c * s) (hz : 0 < z) (hextended : c * z ≤ e * u) : b * z ≤ e * s := by
  have h1 : b * u * z ≤ c * s * z := Int.mul_le_mul_of_nonneg_right hnearer (by omega)
  have h2 : c * z * s ≤ e * u * s :=
    Int.mul_le_mul_of_nonneg_right hextended (by have := h.s_pos; omega)
  have h3 : u * (b * z) ≤ u * (e * s) := by grind
  exact Int.le_of_mul_le_mul_left h3 h.u_pos

/-! ## A candidate that matches one distance exactly pins the comparison -/

/--
A candidate matching the loop candidate's distance exactly, while no closer than the extended
candidate, forces the extended candidate to be at least as near.
-/
public theorem extended_nearer_of_match (h : Bracketing m n l b c r s t u)
    (hz : 0 < z) (hextended : c * z ≤ e * u) (hmatch : b * z = e * s) : c * s ≤ b * u := by
  have h1 : c * z * s ≤ e * u * s :=
    Int.mul_le_mul_of_nonneg_right hextended (by have := h.s_pos; omega)
  have h2 : b * z * u = e * s * u := by rw [hmatch]
  exact Int.le_of_mul_le_mul_left (show z * (c * s) ≤ z * (b * u) by grind) hz

/-- Symmetrically, a candidate matching the extended candidate's distance exactly. -/
public theorem loop_nearer_of_match (h : Bracketing m n l b c r s t u)
    (hz : 0 < z) (hloop : b * z ≤ e * s) (hmatch : c * z = e * u) : b * u ≤ c * s := by
  have h1 : b * z * u ≤ e * s * u :=
    Int.mul_le_mul_of_nonneg_right hloop (by have := h.u_pos; omega)
  have h2 : c * z * s = e * u * s := by rw [hmatch]
  exact Int.le_of_mul_le_mul_left (show z * (b * u) ≤ z * (c * s) by grind) hz

/--
On an exact tie, a candidate matching the loop candidate's distance matches the extended
candidate's too.
-/
public theorem extended_match_of_tie (h : Bracketing m n l b c r s t u)
    (htie : b * u = c * s) (hmatch : b * z = e * s) : c * z = e * u := by
  have h1 : b * z * u = e * s * u := by rw [hmatch]
  have h2 : b * u * z = c * s * z := by rw [htie]
  exact Int.eq_of_mul_eq_mul_left (show s ≠ 0 by have := h.s_pos; omega) (by grind)

end Bracketing
