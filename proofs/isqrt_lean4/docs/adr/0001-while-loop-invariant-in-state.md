# Bundle the loop invariant into the state type, not into `pyWhile`

To faithfully represent a simple Python `while` loop in Lean (for the iterative
`isqrt`), we define a generic combinator `pyWhile` (in `Isqrt/While.lean`) that
takes a guard, a body, an ℕ-valued measure, and a measure-decrease proof, and
returns `{ s : σ // ¬ guard s }`. The loop body cannot be a total `σ → σ` over
raw integers: it evaluates `py<<`, `py>>`, and `py//`, each of which demands a
precondition proof that holds only under the loop invariant (`a > 0`, shift
amounts nonneg, …) and not from the guard alone. **We decided to carry that
invariant by making the caller's `σ` a subtype that bundles it** — exactly as
`isqrt_aux` returns `{ a : ℤ // 0 < a }` — rather than threading an explicit
invariant predicate through `pyWhile`.

## Agreed signature

```lean
def pyWhile {σ : Type}
    (guard : σ → Prop) [DecidablePred guard]
    (body  : (s : σ) → guard s → σ)
    (s₀    : σ)
    (μ     : σ → ℕ)
    (hμ    : ∀ (s : σ) (h : guard s), μ (body s h) < μ s) :
    { s : σ // ¬ guard s } :=
  if h : guard s₀ then pyWhile guard body (body s₀ h) μ hμ
  else ⟨s₀, h⟩
termination_by μ s₀
decreasing_by exact hμ s₀ h
```

The non-proof arguments `guard`, `body`, `s₀` are grouped first; the termination
evidence `μ`, `hμ` trails as part (d). To be paired with explicit `pyWhile_pos`
(step) and `pyWhile_neg` (stop) equation lemmas, which drive the `#guard` tests.

### Companion lemma: post-hoc invariants

Bundling the invariant into `σ` does *not* preclude Hoare-style invariant
reasoning — the two operate at different times and compose. `σ` carries only the
**minimal well-definedness invariant** (enough to discharge the body's py-op
preconditions: `a > 0`, shift-nonnegativity, …). Any *richer* loop invariant —
notably the near-√ property — is proved after the fact via a generic companion
lemma, the standard partial-correctness while rule:

```lean
theorem pyWhile_invariant {σ : Type} {guard : σ → Prop} [DecidablePred guard]
    {body : (s : σ) → guard s → σ} {μ : σ → ℕ}
    {hμ : ∀ s (h : guard s), μ (body s h) < μ s}
    {P : σ → Prop} (s₀ : σ)
    (hinit : P s₀)
    (hstep : ∀ s (h : guard s), P s → P (body s h)) :
    P (pyWhile guard body s₀ μ hμ).val
```

Provable directly from `pyWhile_pos`/`pyWhile_neg` by well-founded induction on
`μ s₀` (or via the generated `pyWhile.induct`). Because `P` ranges over the
subtype `σ`, proving `hstep` has the minimal in-`σ` invariant (`s.property`) in
scope — so the two layers are synergistic. The loop postcondition assembles as
`P (result) ∧ ¬ guard (result)`, the latter from the return subtype's proof.

## Considered options

- **Invariant bundled into `σ` (chosen).** `pyWhile` stays fully generic and
  never mentions an invariant; `body : (s : σ) → guard s → σ` gets its op
  preconditions from the proof riding inside `σ`, and the returned
  `{ s : σ // ¬ guard s }` carries both the invariant and guard-falsity, so the
  caller proves the loop correct with *no induction of their own* — only
  `Inv` at the seed and `Inv`-preservation inside `body`. Consistent with the
  existing `isqrt_aux` subtype-return idiom.
- **Explicit invariant parameter (rejected).** A Hoare-style `pyWhile` taking
  `I : σ → Prop`, a seed proof, a preservation proof, and a body
  `(s : σ) → I s → guard s → σ`. More textbook and arguably more reusable, but a
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
