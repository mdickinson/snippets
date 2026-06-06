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
  argument). This keeps `While.lean`'s imports to just `Mathlib.Data.Nat.Init`
  (for `ℕ`/`Nat.strong_induction_on`); it avoids `conv_lhs` (Mathlib-only) and
  the heavy `import Mathlib.Tactic`.
