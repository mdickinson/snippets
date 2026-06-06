/-
A generic combinator `pyWhile` representing a simple Python `while` loop,
together with its equation lemmas and the partial-correctness while rule.

"Simple" means: no `else` clause, no `break`/`continue`, and no exceptions
raised by the loop machinery itself. The combinator is generic over the loop
state type `σ` and takes:

  - a `guard : σ → Prop` (Python's `while <guard>:`),
  - a `body : (s : σ) → guard s → σ` (one execution of the loop body; the
    `guard s` proof is in scope so the body can discharge any precondition that
    holds only when the guard is true),
  - a measure `μ : σ → ℕ` that strictly decreases each iteration, and
  - the decrease proof `hμ`,

and returns `{ s : σ // ¬ guard s }`: the final state, packaged with the proof
that the guard is now false.

The well-definedness invariant a loop body needs (for isqrt: `a > 0`, shift
amounts nonneg, …) is carried by making the caller's `σ` a subtype that bundles
it — `pyWhile` itself never mentions an invariant. Richer loop properties are
proved after the fact about the result via `pyWhile_invariant`. See
`docs/adr/0001-while-loop-invariant-in-state.md` for the design.
-/

import Mathlib.Data.Nat.Init

/-! ## The combinator -/

/-- A simple Python `while` loop as a Lean combinator.

Runs `body` while `guard` holds, starting from `s₀`, and returns the final
state bundled with a proof that `guard` is false there. `μ` is a measure that
`hμ` shows strictly decreases on every iteration, witnessing termination. -/
def pyWhile {σ : Type}
    (guard : σ → Prop) [DecidablePred guard]
    (body : (s : σ) → guard s → σ)
    (s₀ : σ)
    (μ : σ → ℕ)
    (hμ : ∀ (s : σ) (h : guard s), μ (body s h) < μ s) :
    { s : σ // ¬ guard s } :=
  if h : guard s₀ then pyWhile guard body (body s₀ h) μ hμ
  else ⟨s₀, h⟩
termination_by μ s₀
decreasing_by exact hμ s₀ h

/-! ## Equation lemmas

`pyWhile` is defined by well-founded recursion, so it does not reduce by `rfl`
and `rw [pyWhile]` does not unfold it; the proofs below go through the generated
`pyWhile.eq_def`. These `.val` equations expose its step/stop behaviour; they
are the form that `pyWhile_invariant` and the tests consume. -/

variable {σ : Type} {guard : σ → Prop} [DecidablePred guard]
  {body : (s : σ) → guard s → σ} {μ : σ → ℕ}
  {hμ : ∀ (s : σ) (h : guard s), μ (body s h) < μ s}

/-- Stop step: when the guard is already false, `pyWhile` returns `s₀`. -/
theorem pyWhile_neg (s₀ : σ) (h : ¬ guard s₀) :
    (pyWhile guard body s₀ μ hμ).val = s₀ := by
  rw [pyWhile.eq_def, dif_neg h]

/-- Loop step: when the guard holds, `pyWhile` continues from `body s₀ h`. -/
theorem pyWhile_pos (s₀ : σ) (h : guard s₀) :
    (pyWhile guard body s₀ μ hμ).val = (pyWhile guard body (body s₀ h) μ hμ).val := by
  -- `rw` rewrites only the (leftmost) LHS occurrence of `pyWhile`, exposing its
  -- `dite`; `dif_pos h` then selects the recursive branch.
  rw [pyWhile.eq_def, dif_pos h]

/-! ## Partial-correctness while rule -/

/-- The standard partial-correctness while rule: a predicate `P` that holds at
the seed state and is preserved by `body` holds at `pyWhile`'s result.

Combined with the result subtype's `¬ guard`, this gives the loop
postcondition `P result ∧ ¬ guard result`. Proved by strong induction on the
measure `μ`. -/
theorem pyWhile_invariant {P : σ → Prop} (s₀ : σ)
    (hinit : P s₀)
    (hstep : ∀ (s : σ) (h : guard s), P s → P (body s h)) :
    P (pyWhile guard body s₀ μ hμ).val := by
  -- Strong induction on the measure value, generalised over the start state.
  suffices h : ∀ (n : ℕ) (s : σ), μ s = n → P s → P (pyWhile guard body s μ hμ).val by
    exact h (μ s₀) s₀ rfl hinit
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hμs hP
    by_cases hg : guard s
    · rw [pyWhile_pos s hg]
      exact ih (μ (body s hg)) (hμs ▸ hμ s hg) (body s hg) rfl (hstep s hg hP)
    · rw [pyWhile_neg s hg]
      exact hP
