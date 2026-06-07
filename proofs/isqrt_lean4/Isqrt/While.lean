/-
A generic combinator `pyWhile` representing a simple Python `while` loop,
together with its equation lemmas and the partial-correctness while rule.

"Simple" means: no `else` clause, no `break`/`continue`, and no exceptions
raised by the loop machinery itself. The combinator is generic over the loop
state type `σ` and takes, in Python's lexical order (state set up before the
loop, then `while <condition>:`, then the body):

  - the `initial` state,
  - a `condition : σ → Prop` (Python's `while <condition>:`),
  - a `body : (s : σ) → condition s → σ` (one execution of the loop body; the
    `condition s` proof is in scope so the body can discharge any precondition
    that holds only when the condition is true),

followed by the termination evidence (which has no Python analogue):

  - a measure `μ : σ → α` into any well-founded-ordered type `α` that strictly
    decreases (under `α`'s well-founded relation) each iteration, and
  - the decrease proof `hμ`.

`α` is most often `ℕ` (where the relation is just `<`), but allowing any
`[WellFoundedRelation α]` admits lexicographic or ordinal measures when no
single `ℕ` will do.

It returns `{ s : σ // ¬ condition s }`: the final state, packaged with the
proof that the condition is now false.

The well-definedness invariant a loop body needs (for isqrt: `a > 0`, shift
amounts nonneg, …) is carried by making the caller's `σ` a subtype that bundles
it, rather than threading an explicit invariant predicate through `pyWhile` — so
`pyWhile` itself never mentions an invariant, mirroring how `isqrt_aux` returns
`{ a : ℤ // 0 < a }`. Richer loop properties (notably the near-√ property) are
proved after the fact about the result via `pyWhile_invariant`, the standard
partial-correctness while rule.

This module depends only on core Lean (well-founded recursion and
`WellFoundedRelation`) — it imports nothing.
-/

/-! ## The combinator -/

/-- A simple Python `while` loop as a Lean combinator.

Runs `body` while `condition` holds, starting from `initial`, and returns the
final state bundled with a proof that `condition` is false there. `μ` is a
measure into a well-founded-ordered type `α` that `hμ` shows strictly decreases
on every iteration (under `α`'s well-founded relation), witnessing
termination. -/
def pyWhile {σ : Type} {α : Type} [WellFoundedRelation α]
    (initial : σ)
    (condition : σ → Prop) [DecidablePred condition]
    (body : (s : σ) → condition s → σ)
    (μ : σ → α)
    (hμ : ∀ (s : σ) (h : condition s), WellFoundedRelation.rel (μ (body s h)) (μ s)) :
    { s : σ // ¬ condition s } :=
  if h : condition initial then pyWhile (body initial h) condition body μ hμ
  else ⟨initial, h⟩
termination_by μ initial
decreasing_by exact hμ initial h

/-! ## Equation lemmas

`pyWhile` is defined by well-founded recursion, so it does not reduce by `rfl`
and `rw [pyWhile]` does not unfold it; the proofs below go through the generated
`pyWhile.eq_def`. These `.val` equations expose its step/stop behaviour; they
are the form that `pyWhile_invariant` and the tests consume. -/

variable {σ : Type} {α : Type} [WellFoundedRelation α]
  {condition : σ → Prop} [DecidablePred condition]
  {body : (s : σ) → condition s → σ} {μ : σ → α}
  {hμ : ∀ (s : σ) (h : condition s), WellFoundedRelation.rel (μ (body s h)) (μ s)}

/-- Stop step: when the condition is already false, `pyWhile` returns
`initial`. -/
theorem pyWhile_neg (initial : σ) (h : ¬ condition initial) :
    (pyWhile initial condition body μ hμ).val = initial := by
  rw [pyWhile.eq_def, dif_neg h]

/-- Loop step: when the condition holds, `pyWhile` continues from
`body initial h`. -/
theorem pyWhile_pos (initial : σ) (h : condition initial) :
    (pyWhile initial condition body μ hμ).val
      = (pyWhile (body initial h) condition body μ hμ).val := by
  -- `rw` rewrites only the (leftmost) LHS occurrence of `pyWhile`, exposing its
  -- `dite`; `dif_pos h` then selects the recursive branch.
  rw [pyWhile.eq_def, dif_pos h]

/-! ## Partial-correctness while rule -/

/-- The standard partial-correctness while rule: a predicate `P` that holds at
the initial state and is preserved by `body` holds at `pyWhile`'s result.

Combined with the result subtype's `¬ condition`, this gives the loop
postcondition `P result ∧ ¬ condition result`. Proved by well-founded induction
on the measure `μ`. -/
theorem pyWhile_invariant {P : σ → Prop} (initial : σ)
    (hinit : P initial)
    (hstep : ∀ (s : σ) (h : condition s), P s → P (body s h)) :
    P (pyWhile initial condition body μ hμ).val := by
  -- The inverse image of `α`'s well-founded relation along `μ` well-orders the
  -- states, so we may do well-founded induction on the start state directly.
  have wf : WellFounded fun s₁ s₂ : σ => WellFoundedRelation.rel (μ s₁) (μ s₂) :=
    InvImage.wf μ WellFoundedRelation.wf
  suffices h : ∀ (s : σ), P s → P (pyWhile s condition body μ hμ).val from
    h initial hinit
  intro s
  induction s using wf.induction with
  | _ s ih =>
    intro hP
    by_cases hg : condition s
    · rw [pyWhile_pos s hg]
      exact ih (body s hg) (hμ s hg) (hstep s hg hP)
    · rw [pyWhile_neg s hg]
      exact hP
