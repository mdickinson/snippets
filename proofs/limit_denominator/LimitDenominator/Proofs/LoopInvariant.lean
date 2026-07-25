module

public import LimitDenominator.Proofs.SupportLemmas

/-!
The loop invariant, transcribing the informal proof's § "Details: loop invariants".

The state is the six integers `a`, `b`, `p`, `q`, `r`, `s`; the target `m / n` and the
denominator limit `l` are fixed. Nothing here mentions the monad or the loop's mechanics —
`loopInvariant_step` is stated as a fact about the *values* the body computes, and
`SimplifiedCorrectness` is what connects it to the `do` block.

The **orientation** — the `v` of the informal proof, always `1` or `-1` — is not carried as
state. It is the derived quantity `p * s - r * q`: multiplying the invariant `(p*s - r*q)v = 1`
through by `v` gives `v = p*s - r*q`, so the invariant clause becomes the plain disjunction
`det` below.
-/

/--
The invariant holding before the loop and after every iteration.

The six clauses of the informal proof, plus `p_eq_one_of_q_eq_zero`. That last clause
formalises the informal proof's observation that `q` is zero only before the loop is entered:
it is a fact about which states are *reachable*, not one the other clauses imply, and the
tie-break argument needs it to know that the loop candidate is the lower of the two bounds in
the one degenerate configuration where both bounds have denominator one.
-/
public structure LoopInvariant (m n l a b p q r s : Int) : Prop where
  /-- The orientation `p * s - r * q` is a unit. -/
  det : p * s - r * q = 1 ∨ p * s - r * q = -1
  /-- The target's numerator, recovered from the state. -/
  numerator : a * r + b * p = m
  /-- The target's denominator, recovered from the state. -/
  denominator : a * s + b * q = n
  b_nonneg : 0 ≤ b
  b_lt_a : b < a
  q_nonneg : 0 ≤ q
  q_le_s : q ≤ s
  s_le_l : s ≤ l
  s_pos : 0 < s
  /-- `q` is zero only in the initial state, where `p` is one. -/
  p_eq_one_of_q_eq_zero : q = 0 → p = 1

namespace LoopInvariant

/-! ## The derived residuals -/

/--
The scaled distance from the target to the previous loop candidate, oriented: expanding `m`
and `n` with `numerator` and `denominator` and collapsing with `det` gives `(p*n - m*q)v = a`.
-/
public theorem numerator_residual {m n l a b p q r s : Int} (h : LoopInvariant m n l a b p q r s) :
    (p * n - m * q) * (p * s - r * q) = a := by
  have := h.det; have := h.numerator; have := h.denominator; grind

/-- Likewise `(m*s - r*n)v = b`: the scaled distance from the target to the loop candidate. -/
public theorem denominator_residual {m n l a b p q r s : Int}
    (h : LoopInvariant m n l a b p q r s) :
    (m * s - r * n) * (p * s - r * q) = b := by
  have := h.det; have := h.numerator; have := h.denominator; grind

/-! ## Establishing and maintaining the invariant -/

/--
The invariant holds of the initial state `(n, m % n, 1, 0, m / n, 1)`, for a positive target
denominator and a denominator limit of at least one.
-/
public theorem initial {m n l : Int} (hn : 0 < n) (hl : 1 ≤ l) :
    LoopInvariant m n l n (m % n) 1 0 (m / n) 1 where
  det := .inl (by omega)
  numerator := by have := Int.mul_ediv_add_emod m n; omega
  denominator := by omega
  b_nonneg := Int.emod_nonneg m (by omega)
  b_lt_a := Int.emod_lt_of_pos m hn
  q_nonneg := by omega
  q_le_s := by omega
  s_le_l := hl
  s_pos := by omega
  p_eq_one_of_q_eq_zero _ := rfl

/--
One iteration preserves the invariant. The quotient `k = a / b` is at least one because
`0 < b < a`, which is what keeps the new denominator `q + k*s` at least the old one.
-/
public theorem step {m n l a b p q r s : Int} (h : LoopInvariant m n l a b p q r s)
    (hb : 0 < b) (hcond : q + a / b * s ≤ l) :
    LoopInvariant m n l b (a % b) r s (p + a / b * r) (q + a / b * s) := by
  have hk : 1 ≤ a / b := (Int.le_ediv_iff_mul_le hb).mpr (by have := h.b_lt_a; omega)
  have hks : s ≤ a / b * s := Int.le_mul_of_one_le_left (by have := h.s_pos; omega) hk
  have hdivmod : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
  exact {
    det := by have := h.det; grind
    numerator := by have := h.numerator; grind
    denominator := by have := h.denominator; grind
    b_nonneg := Int.emod_nonneg a (by omega)
    b_lt_a := Int.emod_lt_of_pos a hb
    q_nonneg := by have := h.s_pos; omega
    q_le_s := by have := h.q_nonneg; omega
    s_le_l := hcond
    s_pos := by have := h.q_nonneg; have := h.s_pos; omega
    p_eq_one_of_q_eq_zero := by have := h.s_pos; omega
  }

end LoopInvariant
