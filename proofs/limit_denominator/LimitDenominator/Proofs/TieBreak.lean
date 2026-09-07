module

public import LimitDenominator.Proofs.Bracket

/-!
Choosing between the two candidates, transcribing the informal proof's two § "Tie-breaking"
sections.

`b * u ≤ c * s` compares the two scaled distances, and `loop_nearer_iff` identifies it with the
`2 * b * u ≤ n` the code actually computes. The comparison then feeds the two subcases in
`Bracket` that need it, `loop_le_of_extended_side` and `extended_lt_of_loop_side`; all this file
adds on its own is that an exact tie settles the denominators the right way round.
-/

namespace Bracketing

variable {m n l b c r s t u v : Int}

/-! ## Which candidate is nearer -/

/--
The comparison the code performs is exactly the comparison of the two scaled distances. Adding
`b * u` to both sides of `b * u ≤ c * s` and using `c * s + b * u = n` gives `2 * b * u ≤ n`.
-/
public theorem loop_nearer_iff (h : Bracketing m n l b c r s t u v) :
    2 * b * u ≤ n ↔ b * u ≤ c * s := by
  have hassoc : 2 * b * u = 2 * (b * u) := by grind
  have := h.denominator
  omega

/-- On an exact tie the loop candidate has the smaller denominator. -/
public theorem s_le_u_of_tie (h : Bracketing m n l b c r s t u v) (htie : b * u = c * s) :
    s ≤ u := by
  have h1 : b * u ≤ c * u := Int.mul_le_mul_of_nonneg_right h.b_le_c (by have := h.u_pos; omega)
  exact Int.le_of_mul_le_mul_left (by omega) h.c_pos

end Bracketing
