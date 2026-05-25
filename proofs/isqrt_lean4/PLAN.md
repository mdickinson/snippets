# Lean 4 port of the isqrt correctness proof

Port of `proofs/isqrt/src/isqrt.lean` (a ~780-line Lean 3 correctness proof of
CPython's recursive `math.isqrt`) to Lean 4 with Mathlib 4, switching from `ℕ`
to `ℤ` to match Python's integer semantics and eliminate truncating-subtraction
gymnastics. Recursive algorithm only; the iterative variant is out of scope.

PR: [#16](https://github.com/mdickinson/snippets/pull/16). All seven phases
complete; `lake build --wfail` clean locally and in CI.

## File structure

```
proofs/isqrt_lean4/
  lakefile.lean
  lean-toolchain
  IsqrtLean4.lean        -- library root (implementation only)
  IsqrtLean4Tests.lean   -- tests root (imports Tests/*)
  IsqrtLean4/
    PythonOps.lean       -- pyFloorDiv, pyRShift, pyLShift, pyBitLength
    FDivLemmas.lean      -- Int.fdiv ordering lemmas + Int↔ℕ bridge
    BitLengthLemmas.lean -- natBitLength / pyBitLength properties
    KeyLemma.lean        -- key_isqrt_lemma + isNearSqrt predicate
    SizeConditions.lean  -- size-condition lemmas (ℕ core + ℤ wrappers)
    Isqrt.lean           -- isqrt_aux, isqrt + correctness proof
    Tests/
      PythonOps.lean
      Isqrt.lean
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
5. **Proof-carrying Python wrappers.** `pyFloorDiv (a b) (hb : b ≠ 0)`,
   `pyRShift (n k) (hk : 0 ≤ k)`, `pyLShift (n k) (hk : 0 ≤ k)`. Each call site
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

### `FDivLemmas.lean` — Floor-division lemmas

- Thin wrappers around `Int.ediv` lemmas via `Int.fdiv_eq_ediv_of_nonneg`:
  `Int.le_fdiv_iff_mul_le`, `Int.fdiv_lt_iff_lt_mul`,
  `Int.lt_fdiv_add_one_mul`, `Int.fdiv_le_fdiv` (monotone in numerator),
  `Int.fdiv_mul_le_self`.
- `Int.toNat_fdiv_of_nonneg` bridges to ℕ: for nonneg `x, y`,
  `(x.fdiv y).toNat = x.toNat / y.toNat`.

### `BitLengthLemmas.lean` — Bit-length properties

- `natBitLength_le_iff`, `lt_natBitLength_iff`, `natBitLength_div_two_pow`,
  `two_pow_pred_natBitLength_le`, `lt_two_pow_natBitLength`. Used by
  `SizeConditions.lean`.

### `Isqrt.lean` — Algorithm definitions

- Termination on `c.toNat`. The decrease lemma `fdiv_two_decreasing` is a
  `private` helper.
- Positivity of the return value is proved once in `isqrt_aux_return_pos`, so
  the recursive call destructure `⟨a, a_pos⟩ := isqrt_aux ...` cleanly carries
  `0 < a` for the `// a` division.
- The default-arg precondition tactic is `by omega`, which suffices at most
  call sites. Exception: when the goal contains `n py>> (... py// ...)`,
  `omega` can't see through `py//` — spell out the proof inline using
  `pyFloorDiv_nonneg`.

### `KeyLemma.lean` — Key algebraic lemma

- `isNearSqrt a n := (a - 1)² < n ∧ n < (a + 1)²`. `key_isqrt_lemma` is stated
  as `isNearSqrt a (n.fdiv (4·M²)) → isNearSqrt (M·a + n.fdiv (4·M·a)) n`
  with positivity + `4·M⁴ ≤ n` side conditions.
- Sub-lemmas `M_le_a`, `n_upper`, `n_lower` take their hypotheses explicitly;
  no `section`/`variable` block.
- Algebraic helpers `close_to` and `square_squeeze` are `private` and
  one-liners via `nlinarith [mul_nonneg ...]`. The pure-`nlinarith` direct
  path on the degree-4 lower bound was not attempted.

### `SizeConditions.lean` — Size-condition lemmas

- Hybrid ℕ/ℤ split. Core lemmas (`size_condition_initial_nat`,
  `size_condition_step_nat`, `M_bound_from_size_nat`) live at ℕ using the
  `natBitLength` infrastructure. ℤ-level corollaries
  (`size_condition_initial`, `size_condition_step`, `M_bound_from_size`)
  bridge via `Int.eq_ofNat_of_zero_le`.
- `hasSizeCondition (c n : ℤ) : Prop := (4:ℤ)^c.toNat ≤ n ∧ n < (4:ℤ)^(c.toNat + 1)`
  packages the invariant carried through the recursion. Not stated in terms of
  `isNearSqrt` since the shape is `4^c`, not `(c-1)²`.
- `big_half_little_half`: `(c - 1)/2 + c/2 + 1 = c` for `0 < c`. The parity
  identity connecting the algorithm's `k = (c-1) py// 2` with the recursive
  `c/2`. Provable by `omega`.

### `Isqrt.lean` (continued) — Correctness

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

## Reference files

- `proofs/isqrt/src/isqrt.lean` — original Lean 3 proof (780 lines); unchanged.
- `proofs/isqrt/leanpkg.toml` — Lean 3 project config; unchanged.
- `snippets/isqrt.py` — Python reference implementations; unchanged.
