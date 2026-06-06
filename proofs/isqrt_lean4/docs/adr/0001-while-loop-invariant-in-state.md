# Bundle the loop invariant into the state type, not into `pyWhile`

To faithfully represent a simple Python `while` loop in Lean (for the iterative
`isqrt`), we define a generic combinator `pyWhile` (in `Isqrt/While.lean`) that
takes the initial state, a condition, a body, an ℕ-valued measure, and a
measure-decrease proof, and returns `{ s : σ // ¬ condition s }`. The loop body
cannot be a total `σ → σ` over raw integers: it evaluates `py<<`, `py>>`, and
`py//`, each of which demands a precondition proof that holds only under the
loop invariant (`a > 0`, shift amounts nonneg, …) and not from the condition
alone. **We decided to carry that
invariant by making the caller's `σ` a subtype that bundles it** — exactly as
`isqrt_aux` returns `{ a : ℤ // 0 < a }` — rather than threading an explicit
invariant predicate through `pyWhile`.

## Agreed signature

```lean
def pyWhile {σ : Type}
    (initial   : σ)
    (condition : σ → Prop) [DecidablePred condition]
    (body      : (s : σ) → condition s → σ)
    (μ         : σ → ℕ)
    (hμ        : ∀ (s : σ) (h : condition s), μ (body s h) < μ s) :
    { s : σ // ¬ condition s } :=
  if h : condition initial then pyWhile (body initial h) condition body μ hμ
  else ⟨initial, h⟩
termination_by μ initial
decreasing_by exact hμ initial h
```

The non-evidence arguments `initial`, `condition`, `body` are grouped first and
ordered to mirror a Python `while` loop (the state is set up before the loop,
then `while <condition>:`, then the body); the termination evidence `μ`, `hμ`
(which has no Python analogue) trails as part (d). The names `condition` /
`initial` were chosen over `guard` / `s₀` for the Python-aware audience. To be
paired with explicit `pyWhile_pos` (step) and `pyWhile_neg` (stop) equation
lemmas, which drive the `#guard` tests.

### Companion lemma: post-hoc invariants

Bundling the invariant into `σ` does *not* preclude Hoare-style invariant
reasoning — the two operate at different times and compose. `σ` carries only the
**minimal well-definedness invariant** (enough to discharge the body's py-op
preconditions: `a > 0`, shift-nonnegativity, …). Any *richer* loop invariant —
notably the near-√ property — is proved after the fact via a generic companion
lemma, the standard partial-correctness while rule:

```lean
theorem pyWhile_invariant {σ : Type} {condition : σ → Prop} [DecidablePred condition]
    {body : (s : σ) → condition s → σ} {μ : σ → ℕ}
    {hμ : ∀ s (h : condition s), μ (body s h) < μ s}
    {P : σ → Prop} (initial : σ)
    (hinit : P initial)
    (hstep : ∀ s (h : condition s), P s → P (body s h)) :
    P (pyWhile initial condition body μ hμ).val
```

Provable directly from `pyWhile_pos`/`pyWhile_neg` by well-founded induction on
`μ initial` (or via the generated `pyWhile.induct`). Because `P` ranges over the
subtype `σ`, proving `hstep` has the minimal in-`σ` invariant (`s.property`) in
scope — so the two layers are synergistic. The loop postcondition assembles as
`P (result) ∧ ¬ condition (result)`, the latter from the return subtype's proof.

## Considered options

- **Invariant bundled into `σ` (chosen).** `pyWhile` stays fully generic and
  never mentions an invariant; `body : (s : σ) → condition s → σ` gets its op
  preconditions from the proof riding inside `σ`, and the returned
  `{ s : σ // ¬ condition s }` carries both the invariant and condition-falsity,
  so the caller proves the loop correct with *no induction of their own* — only
  `Inv` at the seed and `Inv`-preservation inside `body`. Consistent with the
  existing `isqrt_aux` subtype-return idiom.
- **Explicit invariant parameter (rejected).** A Hoare-style `pyWhile` taking
  `I : σ → Prop`, a seed proof, a preservation proof, and a body
  `(s : σ) → I s → condition s → σ`. More textbook and arguably more reusable, but a
  longer argument list, a `σ` whose type depends on `I` in the body signature,
  and a second invariant concept living outside `σ`. Rejected for consistency
  and for the cleaner "postcondition falls out of the return type" story.
- **Total raw body + separate safety proof (rejected).** Use raw `Int.fdiv` /
  shifts (junk-on-bad-input) and prove no precondition was violated afterward.
  Abandons the proof-carrying-op fidelity the project rests on and forfeits the
  "no `ZeroDivisionError` / `ValueError`" call-site certificates.

## Consequences

- `σ`'s invariant is kept *minimal* — only what the body needs to typecheck
  (discharge the py-op preconditions). Richer invariants, including the near-√
  property, are proved post-hoc via `pyWhile_invariant` (see above) rather than
  forced into `σ`. This keeps the body's preservation obligation small and the
  interesting algebra (the analogue of `key_isqrt_lemma`) in a separate lemma.
- The combinator is reusable across loops; each caller designs a bespoke subtype
  `σ` carrying its well-definedness invariant, and reaches for `pyWhile_invariant`
  whenever a property isn't already baked into `σ`.
- We get the explicit-invariant design's main benefit (Hoare-style invariant
  reasoning) without paying its cost (a heavier combinator signature): the
  invariant rule is a *derived lemma*, not a parameter of `pyWhile`.

## Implementation notes (from building `Isqrt/While.lean`)

Status: `pyWhile`, the `.val` equation lemmas `pyWhile_pos`/`pyWhile_neg`, and
`pyWhile_invariant` are implemented and tested (toys in `Isqrt/Tests/While.lean`,
including a subtype-`σ` toy whose body re-derives its invariant). Gotchas learned
that the *iterative isqrt* work will hit:

- **`σ` must carry `0 ≤ s` (the variant's nonnegativity), not just the py-op
  preconditions.** The measure is `μ : σ → ℕ`, but the isqrt variant `s` is an
  `ℤ` that stays `≥ 0`, so `μ := fun st => st.val.s.toNat`. Proving `hμ`
  (strict decrease) needs `0 ≤ s` *and* `0 ≤ s'` in scope to reason about
  `.toNat` ordering — `omega` only relates `toNat`s when it knows both are
  nonneg. So `0 ≤ s` belongs in `σ`'s **well-definedness** invariant. This
  widens "minimal `σ`" slightly beyond the py-op preconditions; the near-√
  property still stays out (post-hoc via `pyWhile_invariant`).
- **The body's precondition proof must be a named lemma**, à la
  `isqrt_aux_return_pos`, *not* an inline `by …` inside the `⟨val, proof⟩`
  subtype constructor passed to `pyWhile`. An inline tactic block there hits an
  elaboration-order bug (the proof metavariable entangles with `hμ`'s goal,
  surfacing as a spurious "no goals to be solved"). The toy `countDownPos` uses
  a named `double_pos`; isqrt should follow the same shape.
- **Applying `pyWhile_invariant` needs two hints.** (a) Annotate `P`'s binder
  type — `(P := fun s : σ => …)`; the bare `fun s => …` leaves `σ` a metavar,
  the projections in `P` fail to resolve, and `DecidablePred` instance search
  gets stuck. (b) Expose the `pyWhile` application first (`unfold <caller-def>`)
  so the conclusion unifies. With those, `exact pyWhile_invariant (P := …) initial …`
  infers `condition`/`body`/`μ`/`hμ` from the goal — no need to spell them out.
- **Equation lemmas: `rw [pyWhile.eq_def, dif_pos/dif_neg h]`.** WF recursion
  doesn't `rfl`/`rw`-unfold, but the generated `pyWhile.eq_def` does the job and
  `rw` touches only the LHS occurrence (the recursive RHS has a different `s`
  argument). It avoids `conv_lhs` (Mathlib-only) and the heavy
  `import Mathlib.Tactic`. (Originally this left `While.lean` importing only
  `Mathlib.Data.Nat.Init`, for `ℕ`/`Nat.strong_induction_on`; the measure
  generalisation below dropped `Nat.strong_induction_on`, so the module now
  imports *nothing* — it is pure core Lean.)

## Generalised the measure beyond ℕ (implemented)

The termination evidence was relaxed from an ℕ measure to a measure into **any
well-founded-ordered type** — `μ : σ → α` with `[WellFoundedRelation α]` —
rather than an arbitrary relation on `σ`. This keeps the equation-compiler
definition, the measure ergonomics, and (for ℕ measures) the existing call sites
essentially unchanged, while admitting lexicographic / ordinal measures when a
single `ℕ` won't do. The shipped signature matches the sketch:

```lean
def pyWhile {σ : Type} {α : Type} [WellFoundedRelation α]
    (initial : σ) (condition : σ → Prop) [DecidablePred condition]
    (body : (s : σ) → condition s → σ)
    (μ : σ → α)
    (hμ : ∀ (s : σ) (h : condition s), WellFoundedRelation.rel (μ (body s h)) (μ s)) :
    { s : σ // ¬ condition s } := …
termination_by μ initial
decreasing_by exact hμ initial h
```

(The "arbitrary relation on `σ` via `WellFounded.fix`" alternative was considered
and rejected — it taxes every call site with a `WellFounded` proof and needs a
`#guard`-computability check.)

Findings from implementing it:

- **Def + equation lemmas: no change** — the equation compiler is retained, so
  `pyWhile_pos`/`pyWhile_neg` stay `rw [pyWhile.eq_def, dif_pos/dif_neg h]`, and
  `decreasing_by exact hμ initial h` works **without** a leading `simp_wf`
  (the equation compiler hands `decreasing_by` the goal in `WellFoundedRelation.rel`
  form, which `hμ` matches directly).
- **`pyWhile_invariant` simplifies, as predicted** — well-founded induction on
  the state directly via `InvImage.wf μ WellFoundedRelation.wf` then
  `induction … using wf.induction`. Today's `μ s = n` bookkeeping (the
  `suffices … (μ initial) initial rfl …` + `hμs ▸` plumbing) is gone; only a
  trivial `suffices ∀ s, P s → …` to generalise the start state remains.
- **ℕ test decrease proofs needed one small nudge, not zero.** The earlier
  scoping pass guessed "≈ zero", which was slightly optimistic. The default
  `WellFoundedRelation ℕ` instance is `sizeOfWFRel` (SizeOf-based —
  *not* `Nat.lt_wfRel`), so the decrease goal reads `WellFoundedRelation.rel a b`,
  which `omega` treats as an opaque atom. `WellFoundedRelation.rel a b` *is*
  defeq to `a < b`, but a type-pinned `show (_ : ℕ) < _` only unfolds the `rel`
  projection to `sizeOf a < sizeOf b` — still opaque to `omega`. The fix is
  `simp_wf` (the very tactic `Algorithm.lean`'s `decreasing_by` uses), which
  unfolds `rel` *and* `sizeOf` to a plain `<`: the toy decrease proofs went from
  `by dsimp only; omega` to `by simp_wf; omega`. One token of friction per call
  site, no structural change.
- **A non-ℕ toy now exercises the generality.** `odometer` in
  `Isqrt/Tests/While.lean` measures into `ℕ ×ₗ ℕ` (lexicographic) for a
  two-counter borrow loop. Its decrease proof discharges a lexicographic `<` via
  `show toLex _ < toLex _; rw [Prod.Lex.lt_iff]; simp only [ofLex_toLex]; split <;> omega`.
  Gotcha: the `simp only [ofLex_toLex]` is load-bearing *before* `split` — it both
  strips the `ofLex (toLex …)` round-trips `Prod.Lex.lt_iff` introduces and
  β-reduces the body, which reaches `hμ` as an un-β-reduced `(fun s _ => if …) s h`;
  without it `split` can't find the `if`.
- **Put the well-founded order on the measure codomain `α`, not the state.** Do
  **not** thread a `[WellFoundedRelation σ]`: instance search can silently pick
  the default `SizeOf`/`Prod.lex` instance over the intended one (the same
  `sizeOfWFRel`-vs-intended hazard the ℕ nudge above is a symptom of).
