# Plan: Port isqrt proof from Lean 3 to Lean 4

## TL;DR

Port `proofs/isqrt/src/isqrt.lean` (a ~780-line correctness proof of CPython's recursive `math.isqrt` algorithm) from Lean 3 to Lean 4, switching from `ℕ` to `ℤ` for the main values to match Python and simplify subtraction handling. Use Mathlib 4 (pinned version) for `ring`, `omega`, and standard lemmas. Focus on the recursive algorithm only (not the iterative variant).

## Status

**All phases complete.** Branch: `isqrt-lean4-proof`. PR: [#16](https://github.com/mdickinson/snippets/pull/16).

- Phase 1 (project setup) — done.
- Phase 2 (`PythonOps`, `FDivLemmas`, `BitLengthLemmas`) — done.
- Phase 3 (`isqrt_aux`, `isqrt` definitions + `#guard` tests) — done.
- Phase 4 (`key_isqrt_lemma`) — done (see implementation notes inline below).
- Phase 5 (`SizeConditions`) — done (see implementation notes inline below).
- Phase 6 (`isqrt_aux_correctness`, `isqrt_is_sqrt`) — done (see implementation notes inline below).
- Phase 7 (final verification) — done: `lake build --wfail` clean locally and in CI, PR description updated.

## Scope

- **In scope:** Recursive `isqrt_aux` + `isqrt`, correctness proof (`isqrt_is_sqrt`), project setup
- **Out of scope:** Iterative method proof (future work), any changes to the Python code

## Key design decisions

1. **Types:** Use `ℤ` throughout — `n`, `c`, and return values — to match the Python signatures as closely as possible. Well-founded recursion on `c : ℤ` requires a bit more work (e.g., proving `c / 2 < c` for `c > 0`), but keeps the Lean code aligned with the Python code.
2. **Mathlib 4:** Use it, pinned to a specific commit. Needed for `ring` (polynomial identities), `Nat.size` / bit-length lemmas, and `Int` lemma library.
3. **`ring` on `ℤ`:** `ℤ` is a `CommRing`, so `ring` works directly. This simplifies the ~15+ polynomial identity steps. Many manual arithmetic lemmas from the Lean 3 proof become unnecessary.
4. **`omega`:** Available in Lean 4 core. Handles linear arithmetic goals that `ring` can't (inequalities).
5. **`sub_elimination` lemmas:** Drop entirely — these existed only to work around Nat truncating subtraction (e.g., turning `(a-1)^2 < n` into `a^2 + 1 < n + 2*a`). With `ℤ`, `(a - 1)^2 < n` is stated directly.
6. **Python-matching operations (proof-carrying arguments):** Define Lean wrappers for Python's `//`, `>>`, and `<<` that require validity proofs at each call site, ensuring we never silently divide by zero or shift by a negative amount:
   - `pyFloorDiv (a b : ℤ) (hb : b ≠ 0) : ℤ := Int.fdiv a b`
   - `pyRShift (n k : ℤ) (hk : 0 ≤ k) : ℤ := Int.fdiv n (2 ^ k.toNat)`
   - `pyLShift (n k : ℤ) (hk : 0 ≤ k) : ℤ := n * (2 ^ k.toNat)`

   Uses `Int.fdiv` (floor division), which matches Python `//` semantics exactly — including for negative operands. Note: `Int.fdiv` is **not** Lean's default `/` operator on `ℤ` (that's `Int.ediv`, which uses Euclidean rounding). The two agree when dividing a nonneg by a positive (which is all `isqrt` does), but differ when signs disagree and the division isn't exact. Each call site must supply the validity proof, guaranteeing no exception can occur.

## Phases

### Phase 1: Project setup

Create a new Lean 4 project at `proofs/isqrt_lean4/` (the existing `proofs/isqrt/` Lean 3 proof is left untouched).

1. Create `proofs/isqrt_lean4/lakefile.lean` (Lean 4 / Lake project)
2. Create `proofs/isqrt_lean4/lean-toolchain` pinning the Lean 4 version (match what Mathlib 4 uses)
3. Add Mathlib 4 as a dependency (pinned commit hash)
4. Create project structure:
   ```
   proofs/isqrt_lean4/
     lakefile.lean
     lean-toolchain
     IsqrtLean4/
       PythonOps.lean    -- pyFloorDiv, pyRShift, pyLShift + lemmas
       Isqrt.lean        -- isqrt_aux, isqrt + correctness proof
   ```
   `PythonOps.lean` may be split into multiple files later if it grows large.
5. Verify `lake build` succeeds with empty files

### Phase 2: Python operations (`PythonOps.lean`)

Define Lean wrappers for Python's `//`, `>>`, and `<<` with proof-carrying arguments, plus the lemmas needed by the isqrt proof. This is likely significant work, especially for floor division.

6. **Definitions:**
   - `pyFloorDiv (a b : ℤ) (hb : b ≠ 0) : ℤ := Int.fdiv a b`
   - `pyRShift (n k : ℤ) (hk : 0 ≤ k) : ℤ := Int.fdiv n (2 ^ k.toNat)`
   - `pyLShift (n k : ℤ) (hk : 0 ≤ k) : ℤ := n * (2 ^ k.toNat)`
   - `pyBitLength (n : ℤ) : ℤ` — matches Python's `int.bit_length()`. Defined via `Nat.size n.natAbs` (or `Nat.log2` + 1, etc.), returning `ℤ`. Returns 0 for `n = 0`.

7. **Key lemmas to establish** (at minimum; more may be needed):
   - Division bounds: `a / b ≤ a` for `0 ≤ a`, `0 < b`; `a < (a / b + 1) * b`
   - Monotonicity: `a ≤ b → a / c ≤ b / c` for `0 < c`
   - Division of division: `(a / b) / c = a / (b * c)` for `0 < b`, `0 < c`
   - Shift-division equivalence: `pyRShift n k = pyFloorDiv n (2^k)`
   - Shift composition / cancellation lemmas
   - Positivity preservation: `0 < a → 0 < b → 0 < a / b` (when `b ≤ a`)
   - Bit length bounds: `0 < n → 2^(pyBitLength n - 1) ≤ n ∧ n < 2^(pyBitLength n)`
   - Bit length and shifts: relationship between `pyBitLength` and `pyRShift`

### Phase 3: Port definitions (~lines 458–610 of original)

8. **`isqrt_aux`**: Port with proof-carrying preconditions and subtype return.
   Preconditions `0 ≤ c` and `0 ≤ n` prevent calling with invalid arguments
   (the stronger size condition `4^c ≤ n < 4^(c+1)` is only required for the
   correctness theorem, not the definition). Returns `{ a : ℤ // 0 < a }` —
   the positivity proof flows naturally (base case returns 1; recursive case
   returns `pyLShift a k + pyFloorDiv (...) a ≥ 1` since `a > 0` from the
   recursive subtype, `pyLShift a k ≥ 1`, and the `pyFloorDiv` term is ≥ 0).
   This also provides `a ≠ 0` for the `pyFloorDiv` call.

   Well-founded recursion via `c / 2 < c` for `0 < c` (termination proof on
   `ℤ`). Uses `pyFloorDiv`, `pyRShift`, `pyLShift` throughout to match the
   Python code. Lean 4 convention: test `c = 0` (not `c ≤ 0`) for parity with
   Python's `c == 0`.

   ```
   def isqrt_aux (c n : ℤ) (_hc : 0 ≤ c) (_hn : 0 ≤ n) : { a : ℤ // 0 < a } :=
     if c = 0 then ⟨1, by omega⟩
     else
       let k := pyFloorDiv (c - 1) 2 (by omega)
       let ⟨a, ha⟩ := isqrt_aux (pyFloorDiv c 2 (by omega))
                                 (pyRShift n (2 * k + 2) ‹..›) ‹..› ‹..›
       ⟨pyLShift a k ‹..› + pyFloorDiv (pyRShift n (k + 2) ‹..›) a (ne_of_gt ha),
        by ...⟩   -- positivity proof
   ```

   The recursive call needs proofs that `0 ≤ pyRShift n (2*k+2)` and
   `0 ≤ pyFloorDiv c 2`, plus `0 ≤ 2*k+2` and `0 ≤ k+2` for the `pyRShift`
   calls — all dischargeable from the preconditions.

9. **`isqrt`**: Port with precondition `0 ≤ n`, using `pyBitLength` directly
   (no `size4`). Extracts the integer from `isqrt_aux`'s subtype result:
    ```
    def isqrt (n : ℤ) (_hn : 0 ≤ n) : ℤ :=
      if h : n = 0 then 0
      else
        let a := (isqrt_aux (pyFloorDiv (pyBitLength n - 1) 2 (by omega))
                            n ‹..› ‹..›).val
        if n < a ^ 2 then a - 1 else a
    ```
    The `n = 0` case is split out so the `else` branch has `n ≠ 0`, which
    combined with `0 ≤ n` gives `0 < n` (and hence `0 ≤ n`) for the
    `isqrt_aux` call.

### Phase 4: Key algebraic lemma (induction step)

The heart of the proof: given an approximate square root `a` of `m = n // (4M²)`,
the combined value `d = M·a + n // (4·M·a)` approximates `√n`. This follows the
informal proof (lines 56–137 of the Lean 3 file) rather than the Lean 3 formal
proof structure. Working in `ℤ` eliminates `sub_elimination`, `exists_add_of_le`,
`lt_equiv`/`le_equiv`, and simplifies algebraic helpers to one-liners.

**File:** `IsqrtLean4/KeyLemma.lean`

**Implementation notes (post-Phase 4):**

- `isNearSqrt a n := (a - 1)² < n ∧ n < (a + 1)²` is now an actual Lean
  `def` in `KeyLemma.lean`. `key_isqrt_lemma` is stated as
  `isNearSqrt a (n.fdiv (4*M²)) → isNearSqrt (M*a + n.fdiv (4*M*a)) n`
  (with the obvious positivity / `4·M⁴ ≤ n` side conditions). Phase 5/6
  lemma statements should use `isNearSqrt` where it fits.
- `Int.lt_fdiv_add_one_mul` (plan's `Int.lt_fdiv_add_one_mul_self`) was
  added to `FDivLemmas.lean`. It gives `x < (x.fdiv k + 1) * k` for `0 < k`.
- No `section`/`variable` block was used; the sub-lemmas (`M_le_a`,
  `n_upper`, `n_lower`) take hypotheses explicitly. The "Setup (section
  parameters)" framing below is descriptive of the math, not the file
  structure.
- `close_to` and `square_squeeze` were implemented as `private` helpers
  with `nlinarith [mul_nonneg ...]` proofs. The "Fallback" pure-`nlinarith`
  approach below was not attempted; the helpers were used as planned.

**Setup (section parameters):**
- `n M a : ℤ` with `hM : 0 < M`, `ha : 0 < a`
- `hM4 : 4 * M ^ 4 ≤ n`
- `ha_lo : (a - 1) ^ 2 < n.fdiv (4 * M ^ 2)`
- `ha_hi : n.fdiv (4 * M ^ 2) < (a + 1) ^ 2`

**Definitions within section:**
- `q := n.fdiv (4 * M * a)`
- `d := M * a + q`

**Main theorem `key_isqrt_lemma`:**
`(d - 1) ^ 2 < n ∧ n < (d + 1) ^ 2`

**Sub-lemmas:**

1. **`M_le_a`**: `M ≤ a`. From `M² ≤ n.fdiv (4*M²)` (via `4*M⁴ ≤ n` and
   `Int.le_fdiv_iff_mul_le`) and `n.fdiv (4*M²) < (a+1)²`, so `M² < (a+1)²`,
   giving `M < a+1`, i.e., `M ≤ a`.

2. **`n_upper`** (analog of Lean 3's `d_large`): `n < 4*M²*(a+1)²`. From `ha_hi`:
   `n.fdiv (4*M²) < (a+1)²` gives `n < (a+1)² * (4*M²)` by `Int.fdiv_lt_iff_lt_mul`.

3. **`n_lower`** (analog of Lean 3's `d_small`): `((a-1)²+1) * (4*M²) ≤ n`. From
   `ha_lo`: `(a-1)² < n.fdiv (4*M²)`, so `(a-1)²+1 ≤ n.fdiv (4*M²)`, hence
   `((a-1)²+1) * (4*M²) ≤ n` by `Int.le_fdiv_iff_mul_le`.

4. **Upper bound `n < (d+1)²`:**
   - From floor div: `n < (q + 1) * (4*M*a)` (via `Int.lt_fdiv_add_one_mul_self`)
   - `(q+1)*(4*M*a) ≤ (M*a + q + 1)²` because `(M*a + q + 1)² - (q+1)*(4*M*a) =
     (M*a - q - 1)² ≥ 0` (i.e., `nlinarith [sq_nonneg (M*a - q - 1)]`)
   - Chain: `n < (q+1)*4Ma ≤ (d+1)²`

5. **Lower bound `(d-1)² < n`:** The harder direction. The Lean 3 approach multiplies
   by `(4*M*a)²` to clear the floor-div term, then uses helper lemmas. In ℤ:

   - **Helper `close_to`**: `x < y + c → y < x + c → x² + y² < c² + 2*x*y`.
     Proof: `nlinarith [sq_nonneg (x - y)]`.
   - **Helper `square_squeeze`**: `a ≤ b → b ≤ c → c ≤ d →
     b² + c² + 2*a*d ≤ a² + d² + 2*b*c`.
     Proof: `nlinarith [sq_nonneg (c - b), sq_nonneg (b - a), sq_nonneg (d - c)]`
     or similar.
   - Apply `close_to` to bounds from `n_upper` and `n_lower`.
   - Apply `square_squeeze` to the chain `4*M² ≤ 4*M*a ≤ 4*M²*a² + 4*M*a*q ≤
     4*M²*a² + n`.
   - Combine via `add_lt_add_of_le_of_lt`, then `ring` verifies polynomial identity.

   **Fallback:** If `nlinarith`/`polyrith` with `sq_nonneg` hints can handle the
   lower bound directly (without `close_to`/`square_squeeze`), skip the helpers.
   Test automation first.

**Existing infrastructure needed:**
- FDivLemmas: `Int.fdiv_mul_le_self`, `Int.le_fdiv_iff_mul_le`, `Int.fdiv_lt_iff_lt_mul`,
  `Int.lt_mul_of_fdiv_lt`, `Int.fdiv_le_fdiv`
- Core: `Int.lt_fdiv_add_one_mul_self`, `Int.fdiv_nonneg`
- Mathlib: `sq_nonneg`, `mul_pos`, `ring`, `linarith`, `nlinarith`, `positivity`

**Naming convention:** `a` = recursive result, `d` = combined result, `M = 2^k`.
This matches the informal proof. (The Lean 3 formal proof swaps `a` and `d`.)

### Phase 5: Connecting lemmas (bit-length → key lemma)

Bridge between `natBitLength`/`pyBitLength` (Phase 2c) and the key lemma's
hypotheses (Phase 4). These ensure the initial and recursive calls to `isqrt_aux`
maintain the "size condition".

**File:** `IsqrtLean4/SizeConditions.lean`

**Implementation notes (post-Phase 5):**

- **Chose hybrid ℕ/ℤ approach.** The three core lemmas
  (`size_condition_initial_nat`, `size_condition_step_nat`,
  `M_bound_from_size_nat`) are stated and proved at ℕ level using the
  `natBitLength` infrastructure. ℤ-level corollaries
  (`size_condition_initial`, `size_condition_step`, `M_bound_from_size`)
  are then proved by reduction to ℕ via `Int.eq_ofNat_of_zero_le`.
- **`hasSizeCondition (c n : ℤ) : Prop`** is introduced as
  `(4:ℤ)^c.toNat ≤ n ∧ n < (4:ℤ)^(c.toNat + 1)`. Phase 6 can carry this
  around the strong induction. (Not stated in terms of `isNearSqrt` since
  the shape is `4^c`, not `(c-1)^2`.)
- **Bridging helper.** Added `Int.toNat_fdiv_of_nonneg` to
  `FDivLemmas.lean`: for nonneg `x, y : ℤ`, `(x.fdiv y).toNat = x.toNat / y.toNat`.
- **`pyRShift`'s default `by omega`** can't see through `pyFloorDiv`, so
  the shift amount's nonnegativity proof in `size_condition_step` is
  spelled out inline. Phase 6 will face the same pattern.
- **Phase 6 hookup.** Phase 6 will call `size_condition_initial` (from
  `isqrt_is_sqrt`), and `size_condition_step` + `M_bound_from_size` (in
  the inductive step of `isqrt_aux_correctness`). The `4·M²` /
  `4·(2^k)²` rewrite needed to match `key_isqrt_lemma`'s `n.fdiv (4·M²)`
  with the algorithm's `n py>> (2k+2)` is left for Phase 6 (a `ring` /
  `pow` identity, not a Phase 5 concern).

**Key definition:** The "size condition" for `(c, n)` is `4^c ≤ n < 4^(c+1)`,
i.e., `2^(2c) ≤ n < 2^(2c+2)`. Since `4^c = 2^(2c)`, this connects to
`natBitLength` via:
- `4^c ≤ n ↔ 2c < natBitLength n` (via `lt_natBitLength_iff`)
- `n < 4^(c+1) ↔ natBitLength n ≤ 2c + 2` (via `natBitLength_le_iff`)

**Key lemmas:**

1. **`size_condition_initial`**: For `0 < n` (at ℕ level), with
   `c = (natBitLength n - 1) / 2`:
   `2^(2*c) ≤ n ∧ n < 2^(2*c + 2)`.

   Proof sketch: `2c ≤ natBitLength n - 1` (from `2*(x/2) ≤ x`) gives the lower
   bound via `two_pow_pred_natBitLength_le`. For the upper bound:
   `natBitLength n ≤ 2c + 2` follows from the relationship
   `c = (natBitLength n - 1) / 2`, then use `lt_two_pow_natBitLength`.

2. **`size_condition_step`**: For `0 < c` (at ℕ level), given
   `2^(2*c) ≤ n ∧ n < 2^(2*c + 2)`, let `k = (c - 1) / 2`,
   `m = n / 2^(2*k + 2)`:
   `2^(2*(c/2)) ≤ m ∧ m < 2^(2*(c/2) + 2)`.

   Proof sketch: Uses `natBitLength_div_two_pow` to relate `natBitLength m` to
   `natBitLength n`, plus a `big_half_little_half`-style identity connecting
   `c + 1`, `(c+1)/2`, and `(c+2)/2`.

3. **`M_bound_from_size`**: For `0 < c` with `2^(2*c) ≤ n`, let `k = (c-1)/2`,
   `M = 2^k`: `4 * M^4 ≤ n`.

   Proof sketch: `4 * M^4 = 4 * 2^(4k) = 2^(4k+2)`. Show `4k + 2 ≤ 2c` from
   `k = (c-1)/2`, then `2^(4k+2) ≤ 2^(2c) ≤ n`.

4. **`big_half_little_half`** (helper, at ℕ level): For `0 < c`:
   `c + 1 = (c + 1) / 2 + (c + 2) / 2`. Or equivalently:
   `c = (c - 1) / 2 + c / 2 + 1` (connecting `k = (c-1)/2` and the recursive
   `c/2`). Prove by case split on parity of `c`.

**Existing infrastructure:** `natBitLength_le_iff`, `lt_natBitLength_iff`,
`natBitLength_div_two_pow`, `two_pow_pred_natBitLength_le`,
`lt_two_pow_natBitLength` from Phase 2c.

### Phase 6: Strong induction and `isqrt_is_sqrt`

Tie everything together with strong induction on `c` and derive the main theorem.

**File:** `IsqrtLean4/Isqrt.lean`

**Implementation notes (post-Phase 6):**

- **Strong induction on `c.toNat`** via `Nat.strong_induction_on`, with the
  numeric witness `cn : ℕ` passed as the first argument and `c.toNat = cn`
  threaded as a hypothesis. The recursion-decrease step uses
  `Int.toNat_fdiv_of_nonneg` to bridge `(c py// 2).toNat = c.toNat / 2`.
- **Unfolding `isqrt_aux` in the inductive case.** Hidden in a private
  helper `isqrt_aux_step_val` that exposes the algorithm's return value as
  `a * 2^k.toNat + (n.fdiv (2^(k+2).toNat)).fdiv a`. The tactic recipe is
  `unfold isqrt_aux; simp [hc_pos.ne']; rfl`. The `rfl` is essential — `simp`
  unfolds the `dif_neg` but leaves the `let`-bindings, which `rfl` then
  closes against the let-bound RHS.
- **Bridge to `key_isqrt_lemma`.** Two `toNat`-on-`ℤ` lemmas `toNat_add_two`
  and `toNat_two_mul_add_two` reduce the shift-amount `.toNat` expressions
  to ℕ arithmetic. `4 * M² = 2^(2k+2)` and `4 * M = 2^(k+2)` are then `ring`
  identities (after `pow_add`).
- **`Int.fdiv_fdiv_eq_fdiv_mul`** exists in Mathlib (`Mathlib.Data.Int.DivMod`)
  with signature `(m : Int) {n k : Int} (hn : 0 ≤ n) (hk : 0 ≤ k) :
  (m.fdiv n).fdiv k = m.fdiv (n * k)`. No new lemma needed.
- **`isqrt_is_sqrt`** unfolds `isqrt` directly with `simp only [hn0, ↓reduceDIte]`
  and `simp only [h_lt, ↓reduceIte]`. The split on `n < a * a` uses
  `not_lt.mp` (cleaner than the deprecated `push_neg`).

**Implementer notes (Phase 6 pickup):**

- **Use `hasSizeCondition` (Phase 5)** as the precondition shape:
  `hasSizeCondition c n := (4:ℤ)^c.toNat ≤ n ∧ n < (4:ℤ)^(c.toNat + 1)`.
  Phase 5 provides `size_condition_initial`, `size_condition_step`, and
  `M_bound_from_size` directly at ℤ. Don't re-derive in ℕ.
- **Strong induction on `c.toNat`.** Since `c : ℤ` with `0 ≤ c`, induct
  on `c.toNat` via `Nat.strong_induction_on` (or write an auxiliary
  ∀-quantified helper indexed by a `ck : ℕ` with `hck : c.toNat = ck`).
  Well-founded recursion on `c` directly works for the definition but is
  awkward for the proof.
- **`pyRShift`'s default `by omega` can't see through `pyFloorDiv`.**
  When the goal contains `n py>> (2 * ((c - 1) py// 2) + 2)`, the default
  tactic for the `0 ≤ ...` precondition will fail. Spell out the proof
  inline (see `size_condition_step` for the pattern), or pre-bind
  `k := (c - 1) py// 2` with `hk_nn : 0 ≤ k` via `pyFloorDiv_nonneg`
  before the `py>>` use.
- **`pyFloorDiv_nonneg` needs a type-annotated context.** `have h : 0 ≤
  (a py// b) := pyFloorDiv_nonneg ...` works; bare `have := ...` does
  not (the implicit `hb : b ≠ 0` can't be resolved without the goal type).
- **Bridging the algorithm and `key_isqrt_lemma`.** The algorithm
  computes `n py>> (2*k + 2) = n.fdiv (2^(2k+2))`. The key lemma needs
  `n.fdiv (4*M²)` with `M = 2^k`. These match since
  `4 * (2^k)² = 2^(2k+2)` — a `pow` identity, no `Phase 5` lemma needed.
- **`Int.fdiv_fdiv_eq_fdiv_mul`** (step (d) below). Check Mathlib first;
  if absent, prove via `Int.fdiv_eq_ediv_of_nonneg` and the analogous
  `Int.ediv_ediv_eq_ediv_mul` (or directly from the floor-div definition).
- **`isqrt_aux` returns `{ a : ℤ // 0 < a }`.** Unwrap with `.val` and
  `.property` (or destructure with `⟨a, ha⟩`). Definition is in
  `Isqrt.lean`; do not redefine.

**Key theorems:**

1. **`isqrt_aux_correctness`**: By strong induction on `c.toNat`:

   For `0 < n` and `hasSizeCondition c n` (i.e. `4^c.toNat ≤ n < 4^(c.toNat+1)`),
   the value `d = (isqrt_aux c n hc hn.le).val` satisfies
   `isNearSqrt d n`, i.e. `(d - 1)^2 < n ∧ n < (d + 1)^2`.

   - **Base case** (`c ≤ 0`): `isqrt_aux c n = 1`. Size condition gives
     `1 ≤ n < 4`, so `0 = (1-1)² < n` and `n < 4 = (1+1)²`. ✓
   - **Inductive case** (`c > 0`):
     (a) Let `k = (c-1)/2`, `M = 2^k`, `m = n / (4*M²)`.
     (b) `size_condition_step` gives `4^(c/2) ≤ m < 4^(c/2+1)`.
     (c) Induction hypothesis gives `(a-1)² < m < (a+1)²` for
         `a = isqrt_aux (c/2) m`.
     (d) Unfold `isqrt_aux c n` to `a*M + n // (4*M*a)`.
     (e) `M_bound_from_size` gives `4*M⁴ ≤ n`.
     (f) Apply `key_isqrt_lemma`.

   Step (d) requires `Int.fdiv_fdiv_eq_fdiv_mul` to show
   `n // 2^(k+2) // a = n // (4*M*a)`.

2. **`isqrt_is_sqrt`**: Main theorem:
   ```
   theorem isqrt_is_sqrt (n : ℤ) (hn : 0 ≤ n) :
     let a := isqrt n in a ^ 2 ≤ n ∧ n < (a + 1) ^ 2
   ```

   - Case `n = 0`: `isqrt 0 = 0`. `0² ≤ 0` and `0 < 1²`. ✓
   - Case `n > 0`: Get `d = isqrt_aux c n` with `(d-1)² < n < (d+1)²` from
     `isqrt_aux_correctness` (using `size_condition_initial` for the precondition).
     Unfold `isqrt`:
     - If `n < d²`: returns `d - 1`. Have `(d-1)² < n < d²`, so `(d-1)² ≤ n`
       and `n < d² = ((d-1)+1)²`. ✓
     - If `n ≥ d²`: returns `d`. Have `d² ≤ n < (d+1)²`. ✓

3. **Tests:** `#guard` checks for `isqrt` on values 0, 1, 2, 3, 4, 8, 9, 15, 16,
   99, 100, 10000.

### Phase 7: Final verification

- `lake build --wfail` passes locally
- CI workflow passes on GitHub Actions
- PR description updated with final status

## Design decisions (revised)

- **Follow the informal proof's logical flow** (lines 56–137 of the Lean 3 file)
  rather than the Lean 3 formal proof structure. The algebraic content is the
  same, but the presentation is cleaner in ℤ.
- **ℤ throughout** (no ℝ): avoid `Real.sqrt` and type coercions. The informal
  proof's use of √n and real division is replaced by multiplying through by
  `(4Ma)²` to stay in ℤ, exactly as the Lean 3 proof does — but with the ℕ
  subtraction gymnastics removed.
- **`nlinarith`/`polyrith` first:** Try automation before introducing helper
  lemmas like `close_to`, `am_gm`, `square_squeeze`. If automation handles
  degree-4 polynomial goals with `sq_nonneg` hints, skip the helpers entirely.
- **Naming:** `a` = recursive result, `d` = combined result, `M = 2^k`.
  This matches the informal proof. (The Lean 3 formal proof swaps `a` and `d`.)
- **ℕ-specific workarounds dropped:** `sub_elimination`, `sub_elimination2`,
  `exists_add_of_le`, `lt_equiv`, `le_equiv` are all unnecessary with ℤ.
  Algebraic helpers (`close_to`, `am_gm`, `square_squeeze`) reduce to
  one-liners via `nlinarith [sq_nonneg ...]`.

## Relevant files

- `proofs/isqrt/src/isqrt.lean` — the existing Lean 3 proof (780 lines); kept as-is for reference
- `proofs/isqrt/leanpkg.toml` — Lean 3 project config; kept as-is
- `proofs/isqrt_lean4/` — new Lean 4 project
- `snippets/isqrt.py` — the Python implementations (reference, not modified)

## Risks and considerations

1. **Nat ↔ Int boundary:** Everything is `ℤ` at the surface, but `natBitLength`
   and `Nat.log2` work on `ℕ` internally. Coercions via `n.toNat` are needed at
   that boundary. Well-founded recursion on `c : ℤ` requires showing
   `c / 2 < c` for `c > 0` and using a measure like `Int.toNat c`.

2. **Division semantics:** Python `//` is floor division. We use `Int.fdiv` (not
   `Int.ediv`/`Int.div`). For positive operands they all agree, so this mainly
   matters if we ever generalize.

3. **`nlinarith` on degree-4 goals:** The lower bound proof in Phase 4 involves
   degree-4 polynomial reasoning. `nlinarith` may need explicit `sq_nonneg` hints
   or product-of-nonneg witnesses. If it can't handle it, we fall back to manual
   helper lemmas (`close_to`, `square_squeeze`) which are still much shorter in ℤ
   than their Lean 3 ℕ counterparts.
