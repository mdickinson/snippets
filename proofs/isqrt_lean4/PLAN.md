# Lean 4 port of the isqrt correctness proof

Port of `proofs/isqrt/src/isqrt.lean` (a ~780-line Lean 3 correctness proof of
CPython's recursive `math.isqrt`) to Lean 4 with Mathlib 4, switching from `ℕ`
to `ℤ` to match Python's integer semantics and eliminate truncating-subtraction
gymnastics. The recursive proof came first; the **iterative** variant
(`isqrt_iterative.py`) is now also being verified by reusing that machinery —
see [Iterative variant](#iterative-variant).

PR: [#16](https://github.com/mdickinson/snippets/pull/16). All seven phases of
the recursive proof complete; `lake build --wfail` clean locally and in CI. The
iterative variant is also complete on the same branch: `isqrtIterative_is_sqrt`
(`Isqrt/IterativeCorrectness.lean`) proves the same statement as
`isqrt_is_sqrt`.

## File structure

```
proofs/isqrt_lean4/
  lakefile.lean
  lean-toolchain
  Isqrt.lean             -- library root (implementation only)
  IsqrtTests.lean        -- tests root (imports Tests/*)
  Isqrt/
    PythonOps.lean       -- pyFloordiv, pyRshift, pyLshift, pyBitLength
    FDivLemmas.lean      -- Int.fdiv ordering lemmas + Int↔ℕ bridge
    BitLengthLemmas.lean -- natBitLength / pyBitLength properties
    RecursionDepth.lean  -- isqrt_c_nonneg, shared by both algorithm modules
    KeyLemma.lean        -- key_isqrt_lemma + isNearSqrt / isIntegerSqrt predicates
    SizeConditions.lean  -- size-condition lemmas (ℕ core + ℤ wrappers)
    Algorithm.lean       -- isqrt_aux and isqrt definitions
    Correctness.lean     -- correctness proofs (isqrt_aux_correctness, isqrt_is_sqrt)
    While.lean           -- generic pyWhile combinator (see ADR 0001)
    Iterative.lean       -- isqrtIterative definition (pyWhile-based) + body lemmas
    IterativeCorrectness.lean -- isqrtIterative_is_sqrt
    Tests/
      PythonOps.lean
      Isqrt.lean
      While.lean
      Iterative.lean
  CONTEXT.md             -- glossary for the while-loop translation
  docs/adr/0001-while-loop-invariant-in-state.md
  PLAN.md
.github/workflows/lean4-isqrt.yml
```

## Key design decisions

1. **`ℤ` throughout** — `n`, `c`, and return values — to match Python signatures
   and eliminate Nat truncating-subtraction workarounds (`sub_elimination`,
   `exists_add_of_le`, `lt_equiv`, `le_equiv`).
2. **Mathlib 4**, pinned via `lakefile.lean` + `lean-toolchain`. Needed for
   `ring`, `nlinarith`, `positivity`, and the `Int` lemma library.
3. **`ring` on `ℤ`** replaces ~15 manual arithmetic lemmas from the Lean 3
   proof; `omega` covers linear inequalities.
4. **`Int.fdiv`**, not `Int.ediv` (Lean's default `/` on `ℤ`), for Python-`//`
   semantics. They agree when dividing nonneg by positive — all `isqrt` does —
   but differ when signs disagree and the division isn't exact.
5. **Proof-carrying Python wrappers.** `pyFloordiv (a b) (hb : b ≠ 0)`,
   `pyRshift (n k) (hk : 0 ≤ k)`, `pyLshift (n k) (hk : 0 ≤ k)`. Each call site
   supplies the validity proof, so no exception can occur.
6. **`isqrt_aux` returns `{ a : ℤ // 0 < a }`.** Positivity flows through the
   subtype so the `// a` division in the recursive case is safe.
7. **Naming.** `a` = recursive result, `d` = combined result, `M = 2^k`. Matches
   the informal proof; the Lean 3 formal proof swapped `a` and `d`.
8. **Follow the informal proof's logical flow** (lines 56–137 of the Lean 3
   file) rather than the Lean 3 formal structure. Same algebraic content,
   cleaner in ℤ. The informal proof's use of `√n` and real division is replaced
   by multiplying through by `(4·M·a)²` to stay in ℤ, exactly as the Lean 3
   proof did — but without the ℕ-subtraction gymnastics.

## Implementation notes

### `PythonOps.lean` — Python operations

- `pyBitLength` is defined via `natBitLength n.natAbs`, where `natBitLength` is
  defined inductively in terms of `Nat.log2`; returns `ℤ`. Matches Python's
  `int.bit_length()` for all inputs.
- Python-operator ordering/arithmetic lemmas that let downstream code reason
  about `py>>`/`py//` without naming `Int.fdiv`: `pyRshift_le_self` (a right
  shift of a nonneg can't grow it), `pyRshift_succ` (`n >> (k+1) = (n >> k) // 2`,
  the halving link), `pyFloordiv_mul_le_self`. These bridge to the `Int.fdiv`
  lemma library, so `PythonOps` now `import`s `FDivLemmas` (acyclic — `FDivLemmas`
  is pure `Int.fdiv`, naming no py-op) and `Mathlib.Data.Int.DivMod`.
- `PythonOps` also `import`s `Mathlib.Tactic.Ring` and `Mathlib.Tactic.Linarith`
  though it uses neither directly: downstream files (`Iterative`,
  `SizeConditions`) call `ring`/`linarith`/`nlinarith` without importing those
  tactics themselves and free-ride on this transitive re-export. Removing them as
  "unused" breaks the downstream build under `--wfail` (a `/simplify` pass hit
  this); the proper fix is to import the tactics in those files directly.

### `FDivLemmas.lean` — Floor-division lemmas

- Thin wrappers around `Int.ediv` lemmas via `Int.fdiv_eq_ediv_of_nonneg`:
  `Int.le_fdiv_iff_mul_le`, `Int.fdiv_lt_iff_lt_mul`,
  `Int.lt_fdiv_add_one_mul`,
  `Int.fdiv_mul_le_self`, `Int.fdiv_le_self_of_nonneg` (a nonneg ÷ positive
  can't grow).
- `Int.toNat_fdiv_of_nonneg` bridges to ℕ: for nonneg `x, y`,
  `(x.fdiv y).toNat = x.toNat / y.toNat`.

### `BitLengthLemmas.lean` — Bit-length properties

- `natBitLength_le_iff`, `lt_natBitLength_iff`,
  `two_pow_pred_natBitLength_le`, `lt_two_pow_natBitLength`. Used by
  `SizeConditions.lean`.
- Right-shift facts in py-op form for `Iterative.lean`:
  `one_le_pyRshift_of_lt_pyBitLength` (`0 ≤ s < c.bit_length() ⟹ 1 ≤ c >> s`)
  and `pyRshift_pyBitLength_eq_zero` (`c >> c.bit_length() = 0`, the loop seed
  value of `d`).

### `RecursionDepth.lean` — Shared recursion depth

- A one-lemma module holding `isqrt_c_nonneg` (`(n.bit_length() - 1) py// 2 ≥ 0`
  for `n ≠ 0`). Both `Algorithm.lean` and `Iterative.lean` compute that depth `c`
  and need it nonneg, so the fact lives here — neither algorithm module imports
  the other (see [Iterative variant](#iterative-variant)). Imports only
  `PythonOps` + `BitLengthLemmas`.

### `Algorithm.lean` — Algorithm definitions

(Correctness proofs split into `Correctness.lean`.)

- Termination on `c.toNat`. The decrease lemma `fdiv_two_decreasing` is a
  `private` helper.
- Positivity of the return value comes from the shared
  `pyLshift_add_pyFloordiv_pos` (in `PythonOps`), specialized here as
  `isqrt_aux_return_pos`, so the recursive call destructure
  `⟨a, a_pos⟩ := isqrt_aux ...` cleanly carries `0 < a` for the `// a` division.
- The default-arg precondition tactic is `by omega`, which suffices at most
  call sites. Exception: when the goal contains `n py>> (... py// ...)`,
  `omega` can't see through `py//` — spell out the proof inline using
  `pyFloordiv_nonneg`.

### `KeyLemma.lean` — Key algebraic lemma

- `isNearSqrt a n := (a-1)*(a-1) < n ∧ n < (a+1)*(a+1)`. `key_isqrt_lemma` is
  stated as `isNearSqrt a (n.fdiv (4·M²)) → isNearSqrt (M·a + n.fdiv (4·M·a)) n`
  with positivity + `4·M⁴ ≤ n` side conditions.
- Companion `isIntegerSqrt a n := a*a ≤ n ∧ n < (a+1)*(a+1)` — the exact
  `a = ⌊√n⌋` postcondition the two `*_is_sqrt` theorems assert. Lives here beside
  `isNearSqrt`; both correctness modules already import `KeyLemma`. The `a-1`/`a`
  return adjustment that narrows `isNearSqrt` to `isIntegerSqrt` is the shared
  lemma `isNearSqrt.toIntegerSqrt`, which closes both `*_is_sqrt` theorems.
- Both predicates use the multiplicative form (parallel to each other, mirroring
  Python, sidestepping `^`). `key_isqrt_lemma`'s internal degree-4 algebra stays
  in `^2`; it bridges `*`↔`^2` (via `pow_two`) only at the predicate boundary —
  destructuring the hypothesis and assembling the conclusion. The base/seed
  cases in the two correctness proofs likewise `show` the `*` form.
- Sub-lemmas `M_le_a`, `n_upper`, `n_lower` take their hypotheses explicitly;
  no `section`/`variable` block.
- Algebraic helpers `close_to` and `square_squeeze` are `private` and
  one-liners via `nlinarith [mul_nonneg ...]`. The pure-`nlinarith` direct
  path on the degree-4 lower bound was not attempted.

### `SizeConditions.lean` — Size-condition lemmas

- Hybrid ℕ/ℤ split. Core lemmas (`size_condition_initial_nat`,
  `size_condition_at_depth_nat`, `M_bound_from_size_nat`) live at ℕ using the
  `natBitLength` infrastructure. ℤ-level corollaries
  (`size_condition_initial`, `size_condition_at_depth`, `M_bound_from_size`)
  bridge via `Int.eq_ofNat_of_zero_le`. `size_condition_step_nat` (and its ℤ
  corollary `size_condition_step`) is in turn the `d = c/2` specialisation of
  `size_condition_at_depth_nat` — see "New lemma" below.
- `hasSizeCondition (c n : ℤ) : Prop := (4:ℤ)^c.toNat ≤ n ∧ n < (4:ℤ)^(c.toNat + 1)`
  packages the invariant carried through the recursion. Not stated in terms of
  `isNearSqrt` since the shape is `4^c`, not `(c-1)²`.
- `big_half_little_half`: `(c - 1)/2 + c/2 + 1 = c` for `0 < c`. The parity
  identity connecting the algorithm's `k = (c-1) py// 2` with the recursive
  `c/2`. Provable by `omega`.

### `Correctness.lean` — Correctness

- Strong induction via `Nat.strong_induction_on` on a `cn : ℕ` parameter, with
  `c.toNat = cn` threaded through. Well-founded recursion on `c : ℤ` directly
  works for the definition but is awkward for the proof.
- `isqrt_aux_step_val` is a `private` unfolding lemma exposing the recursive
  return value as `a * 2^k.toNat + (n.fdiv (2^(k+2).toNat)).fdiv a`. Tactic
  recipe: `unfold isqrt_aux; simp [hc_pos.ne']; rfl`. The trailing `rfl` is
  essential — `simp` reduces the `dif_neg` but leaves let-bindings that `rfl`
  closes.
- Bridges to `key_isqrt_lemma`: two private `toNat`-on-`ℤ` lemmas
  (`toNat_add_two`, `toNat_two_mul_add_two`) plus the power identities
  `4·M² = 2^(2k+2)` and `4·M = 2^(k+2)` (one `ring` step after `pow_add`).
- `Int.fdiv_fdiv_eq_fdiv_mul` is already in Mathlib's
  `Mathlib.Data.Int.DivMod` (`(m.fdiv n).fdiv k = m.fdiv (n * k)` for
  `0 ≤ n, k`) — no new lemma needed.
- `isqrt_is_sqrt` unfolds `isqrt` with `simp only [hn0, ↓reduceDIte]` and
  `simp only [h_lt, ↓reduceIte]`. Split on `n < a * a` uses `not_lt.mp`
  (cleaner than the deprecated `push_neg`).

## Iterative variant

The iterative form — CPython's bottom-up unrolling of the recursive `isqrt_aux`
into a `while s >= 0` loop, transcribed (lightly rewritten) at the top of
`Isqrt/Iterative.lean` — is proved correct — theorem `isqrtIterative_is_sqrt`,
the same statement as `isqrt_is_sqrt` (standalone, not via equivalence to the
recursive form) — by *reusing* the recursive proof's algebra (`key_isqrt_lemma`,
the size-condition lemmas) through the generic `pyWhile` combinator
(`Isqrt/While.lean`, ADR 0001) and its post-hoc invariant rule `pyWhile_invariant`.

### The bottom-up correspondence

Persistent loop state is `(s, d, a)`; `e` is loop-local (the incoming `d`);
`c, n` are fixed (closure-captured). With `L = c.bit_length()`:

- Invariant `d = c >> (s+1)`: the loop variable `s` runs `L−1 … 0` (then `−1` at
  exit), and the persistent `d` holds the *previous* iteration's shift
  `c >> (s+1)`, climbing the chain `c >> j` that the recursion descends. Seed
  `s = L−1`, `d = c >> L = 0`.
- In the body `e = d` (the incoming `d`, `= c >> (s+1)`) then `d = c >> s` (the
  new `d`), so `e = d // 2` (the recursion's `c // 2` link); the left-shift
  amount `d − e − 1 = (d−1)//2 = k` is the recursive `k`, and the right-shift
  amount is `2c − d − e + 1 = 2(c−d) + 2k + 2`.
- One iteration is therefore one `key_isqrt_lemma` step at parent `d`, `M = 2^k`,
  on **`n` at depth `d`**: `N_d = ⌊n / 4^(c−d)⌋` (see `CONTEXT.md`).

### State subtype σ (well-definedness invariant — minimal, per ADR 0001)

`σ`'s invariant `iterInv` is a `Prop`-valued **`structure`** (not a bare
conjunction) with four fields, each discharging a body obligation:

- `hs_lb : −1 ≤ s` — the loop variable's lower bound, so the shift amount `s + 1`
  is nonneg. It is a `structure` precisely so this field is in scope when the
  next field's `c py>> (s+1)` discharges its `0 ≤ s+1` precondition — a plain `∧`
  cannot share a proof between conjuncts.
- `hs_lt : s < c.bit_length()` — forces `d_new = c >> s ≥ 1`, so `d_new − e − 1 ≥ 0`
  (uses `2^(L−1) ≤ c`, via `one_le_pyRshift_of_lt_pyBitLength`).
- `hd_eq : d = c py>> (s+1)` — identifies the incoming `e = d` as `c >> (s+1)`,
  giving `e = d_new // 2` (where `d_new = c >> s`, via `pyRshift_succ`) and
  `e, d_new ≤ c` for the right shift (`pyRshift_le_self`).
- `ha_pos : 0 < a` — the `py// a` precondition.

The whole invariant — like all of `Iterative.lean` — is phrased in the Python
operators `py//`/`py>>`/`py<<` with no explicit `Int.fdiv`; the `fdiv`-level
facts are factored into `PythonOps`/`FDivLemmas`/`BitLengthLemmas`. A `structure`
rather than an `Exists`-wrapped conjunction because `iterBody` *constructs data*
(an `IterState`) while reading `hd_eq` off `st.property`, and one cannot project a
witness out of `Exists` in a data context (large elimination) — whereas all-`Prop`
structure fields project freely (like `And.left`).

The full `0 ≤ s` is **not** in `σ` (only `−1 ≤ s` is): the loop condition supplies
the strict bound fresh wherever needed (the `c >> s` shift and the measure's strict
decrease). The measure is `(s+1).toNat`, not `s.toNat` — the loop runs down to
`s = −1`, where `s.toNat` would stall at the final `0 → −1` step. The near-√
property and the size condition are deliberately **not** in `σ` either.

### Loop property P (post-hoc, via `pyWhile_invariant`)

`P (s,d,a) := isNearSqrt a N_d`, ranging over `σ` (so `st.property` — the
well-definedness invariant — is in scope in the preservation step). Near-√
**only**; the size condition is pulled fresh from `size_condition_at_depth` (a
`(c,n)`-only fact) at both seed and step rather than threaded through the loop.

**The loop is a named `def`.** `isqrtIterative` calls `isqrtIterativeLoop`
(returning the post-loop `{ st : IterSigma c // ¬ (0 ≤ st.val.s) }` — `σ` is
itself a subtype, hence `st.val.s`); the `while` body is no longer inline. This is what makes `pyWhile_invariant` usable: the proof
`unfold`s `isqrtIterativeLoop` to expose the bare `pyWhile` application, then
`refine pyWhile_invariant (P := …) _ ?hinit ?hstep` unifies the goal to fill the
implicit `condition`/`body`/`μ`/`hμ` — so the opaque measure-decrease proof term
never has to be written out. (This is the `countDownPos` pattern from
`Tests/While.lean`.) The step's depth bounds `d_old, d_new ≤ c` come from
`Int.fdiv_le_self_of_nonneg` (in `FDivLemmas`).

The `hstep` algebra rewrites the body's new `a` (via `iterBody_a`) into the
`key_isqrt_lemma` output `M·a + ⌊N_new/4Ma⌋` with `M = 2^k`, `k = (d_new−1)//2`.
The two exponent bridges — divisor `4^(c−d_new)·4M² = 4^(c−d_old)` and
`4^(c−d_new)·4M = 2^(2c−d_new−d_old+1)` — are each discharged by rewriting all
powers to base 2 (`4 = 2^2`, `M = 2^k`), collapsing with
`simp only [← pow_mul, ← pow_add]`, then `congr 1; omega` on the ℕ exponents
(`omega` handles the `.toNat`s given `k = d_new − d_old − 1`, itself proved by
`fdiv→ediv` + `omega` from `d_old = d_new // 2`).

- Seed `d = 0`: `isNearSqrt 1 ⌊n/4^c⌋`, true since `⌊n/4^c⌋ ∈ {1,2,3}` — the
  recursion's base case `isqrt_aux 0 m = 1`.
- Step: `key_isqrt_lemma` at `M = 2^k`; needs `4M⁴ ≤ N_{d_new}` (from
  `size_condition_at_depth` then `M_bound_from_size`) and
  `isNearSqrt a (N_{d_new}.fdiv 4M²)` = `isNearSqrt a N_{d_old}` = old `P`
  (exponent bridge `c − d_new + k + 1 = c − d_old`, mirroring `isqrt_aux_step_val`).
- Exit `s < 0 ⟹ (s+1).toNat = 0 ⟹ d = c >> 0 = c ⟹ N_c = n`: `P` collapses to
  `isNearSqrt a n`, then the return line `a − 1 if a*a > n else a` picks `⌊√n⌋`
  exactly as `isqrt_is_sqrt` does off its `n < a*a` branch (same function, now
  phrased identically).

### New lemma: `size_condition_at_depth`

In `SizeConditions.lean`: from `hasSizeCondition c n` and `0 ≤ d ≤ c`, conclude
`hasSizeCondition d ⌊n/4^(c−d)⌋`. The ℕ core is two steps —
`4^d · 4^(c−d) = 4^c ≤ n` (`Nat.le_div_iff_mul_le`) and
`n < 4^(c+1) = 4^(d+1) · 4^(c−d)` (`Nat.div_lt_iff_lt_mul`) — then the usual
`Int.eq_ofNat_of_zero_le` bridge to ℤ. It *cannot* be iterated bottom-up from the
child's condition (floor division loses information), hence the direct proof from
the top condition.

The recursive proof's `size_condition_step_nat` is now derived as the `d = c/2`
corollary of this lemma: its step divisor `2^(2k+2)` (`k = (c−1)/2`) equals the
depth-`c/2` divisor `4^(c − c/2)`, since `2k+2 = 2(c − c/2)` by
`big_half_little_half`. So the two size-preservation facts share one core proof.

### n = 0

The snippet is unsound at `n = 0` (`c = −1` → negative shift). `isqrtIterative`
special-cases `n = 0 → 0` before the loop, mirroring the recursive `isqrt`;
precondition `0 ≤ n`. Every `n ≥ 1` runs the loop faithfully (`n ≤ 3` gives
`c = 0`, so the loop is skipped).

### Body precondition lemmas (named, per ADR 0001 gotcha)

The body's py-op preconditions and `0 < a_new` are discharged by **top-level
named lemmas**, not inline `by` inside the `⟨val, proof⟩` constructor (that hits
the elaboration-order metavar bug → spurious "no goals"). The shared
`pyLshift_add_pyFloordiv_pos` (`PythonOps`) proves
`0 < (a py<< K) + (n py>> J) py// a` for `a>0, n≥0, K≥0, J≥0`; the iterative body
uses it directly, and `isqrt_aux`'s recursive return is its `k`, `k+2`
specialization (`isqrt_aux_return_pos`). Measure decrease is
`by simp_wf; omega` (the default `WellFoundedRelation ℕ` is `sizeOfWFRel`, opaque
to bare `omega`).

### Build gotchas hit in `Iterative.lean`

- **The `py<<` / `py>>` / `py//` infixes take only their two operands** — the
  precondition proof can't ride through (`a py<< k hK` parses as `(a py<< k) hK`
  → "function expected"). Either keep the nonneg fact as a `have` in scope and
  let the operator's default `:= by omega` find it (as `isqrt_aux` does, and as
  `iterBody` now does), or call `pyLshift`/`pyRshift`/`pyFloordiv` in prefix form
  with the proof. Making `iterBody` a standalone `def` (not inline in the
  `pyWhile` call) gives full tactic freedom and sidesteps the ADR's inline-`by`
  entanglement.
- **`pyWhile` returns `{ s : σ // ¬ condition s }` and here `σ` is itself a
  subtype**, so the loop's final `a` is `result.val.val.a` (two `.val`s).
- **`omega` does not reduce structure projections** like `{ s := …, … }.s`; use
  `show <reduced goal>` first (the constructor form is defeq but omega atomises
  it).
- **`Int.fdiv_eq_ediv_of_nonneg x h`'s `h : 0 ≤ b` picks the *divisor* `b`**, not
  the dividend — passing the dividend's nonnegativity rewrites the wrong term.
- With `iterBody_s` marked `@[simp]`, `simp_wf` reduces the measure goal (the
  `(s+1).toNat` strict decrease) to something `omega` closes from the loop
  condition `0 ≤ s`; the decrease proof is just `simp_wf; omega` (no explicit `rw`).

## Reference files

- `proofs/isqrt/src/isqrt.lean` — original Lean 3 proof (780 lines); unchanged.
- `proofs/isqrt/leanpkg.toml` — Lean 3 project config; unchanged.
- `snippets/isqrt.py` — Python reference implementations; unchanged.
