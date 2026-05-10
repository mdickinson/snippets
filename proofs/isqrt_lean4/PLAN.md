# Plan: Port isqrt proof from Lean 3 to Lean 4

## TL;DR

Port `proofs/isqrt/src/isqrt.lean` (a ~780-line correctness proof of CPython's recursive `math.isqrt` algorithm) from Lean 3 to Lean 4, switching from `ℕ` to `ℤ` for the main values to match Python and simplify subtraction handling. Use Mathlib 4 (pinned version) for `ring`, `omega`, and standard lemmas. Focus on the recursive algorithm only (not the iterative variant).

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

8. **`isqrt_aux`**: Port as `isqrt_aux : ℤ → ℤ → ℤ` with both `c : ℤ` and `n : ℤ`. Well-founded recursion via `c / 2 < c` for `0 < c` (needs a termination proof on `ℤ`). Express shifts as division/multiplication by powers of 2:
   ```
   isqrt_aux c n =
     if c ≤ 0 then 1
     else
       let k := (c - 1) / 2
       let a := isqrt_aux (c / 2) (n / 4^(k+1))
       a * 2^k + (n / 2^(k+1)) / a
   ```

9. **`isqrt`**: Port as `isqrt : ℤ → ℤ`, using `pyBitLength` directly (no `size4`):
    ```
    isqrt n =
      if n ≤ 0 then 0
      else
        let a := isqrt_aux ((pyBitLength n - 1) / 2) n
        if n < a^2 then a - 1 else a
    ```

### Phase 4: Port helper lemmas (~lines 148–335 of original)

11. **Drop lemmas made unnecessary by `ℤ`:**
   - `sub_elimination`, `sub_elimination2` — Nat subtraction workarounds
   - `lt_iff_not_le`, `le_iff_not_lt` — available in Mathlib/core
   - `le_iff_lt_succ` — available in Mathlib/core
   - `lt_of_mul_lt_mul` — available in Mathlib
   - `exists_add_of_le` — used extensively for "eliminate subtraction by introducing c where b = a + c"; less needed with Int
   - `Nat.mul_lt_of_lt_div` — available in Mathlib
   - `self_lt_div_succ_mul` — rephrase for Int

12. **Keep and port (adapting to ℤ):**
    - `square_lt_square`, `square_le_square`, `lt_of_square_lt_square` — may exist in Mathlib for Int; check first, define if not
    - `close_to` — key lemma: `a < b + c → b < a + c → a^2 + b^2 < c^2 + 2*a*b`. With `ℤ`, the proof simplifies: expand and use `ring` to reduce to `0 < (c - b + a)(c + b - a)`, then reason from hypotheses. No need for the `close_to_sublemma` / case split on `a ≤ b`.
    - `am_gm` — `4*a*b ≤ (a + b)^2`. With `ℤ`: `(a + b)^2 - 4*a*b = (a - b)^2 ≥ 0`. Clean one-liner with `ring` + `sq_nonneg`.
    - `square_squeeze` — port with `ring`
    - `lt_equiv`, `le_equiv` — small utility lemmas for "deduce c < d from a < b given a + d = b + c"; with `ℤ` these might be replaceable by `linarith` or `omega` at call sites

### Phase 5: Port `key_isqrt_lemma` — induction step (~lines 337–460 of original)

13. **Restate with `ℤ`:** The section parameters become:
    - `n : ℤ`, `M : ℤ`, `d : ℤ` (was `ℕ`)
    - `M_pos : 1 ≤ M`
    - `n_lower_bound : 4 * M^4 ≤ n`
    - `d_bounds : let m := n / (4 * M^2); (d - 1)^2 < m ∧ m < (d + 1)^2`
    - Note: the `1 ≤ d` condition is now *derivable* from `d_bounds` rather than stated separately (since `(d-1)^2 < m` and `m ≥ 0` gives `d ≥ 0`, and `m < (d+1)^2` with `m ≥ 1` gives `d ≥ 1`)

14. **Port the sub-lemmas** (`key_inequality`, `d_large`, `d_small`, etc.) adapting to `ℤ`. Many become simpler:
    - `key_inequality`: `M ≤ d` (same reasoning, cleaner with `ℤ`)
    - `d_large`, `d_small`: direct from `d_bounds` and algebra, using `ring` + inequalities
    - The final `key_isqrt_lemma_lhs` and `key_isqrt_lemma_rhs` — the two main bound proofs

15. **Port `key_isqrt_lemma`:** Combines the above.

### Phase 6: Port bit-length lemmas + correctness (~lines 462–780 of original)

16. **Bit-length / power-of-4 lemmas:** Establish the relationship between `pyBitLength` and the bounds on `c` that the proof needs. The Lean 3 proof's `size4` lemmas (`size4_le_iff_lt_exp4`, `size4_shift`, `size4_condition_initial`, `size4_condition_step`) are re-expressed in terms of `pyBitLength`. Key facts:
    - The initial `c = (pyBitLength n - 1) / 2` satisfies `4^c ≤ n < 4^(c+1)` (i.e., `c + 1` is the number of base-4 digits)
    - After shifting, the recursive call's `c` satisfies the same invariant for the shifted `n`

17. **`big_half_little_half`:** Port `n = (n + 1) / 2 + n / 2`. May be available in Mathlib (on `ℤ` or `ℕ`).

18. **`isqrt_aux_base`:** Base case (c = 0). With `ℤ`: show `(1-1)^2 < n ∧ n < (1+1)^2`, i.e., `0 < n ∧ n < 4`.

19. **`isqrt_aux_M_bound`:** Port the bound `4 * (2^k)^4 ≤ n` derivation.

20. **`isqrt_aux_step`:** Port the reduction step, connecting to `key_isqrt_lemma`.

21. **`isqrt_aux_correctness`:** Strong induction on `c : ℤ` (via well-founded relation on `Int.toNat` or similar). Statement: for `n : ℤ` with the appropriate bit-length condition on `c`, the result satisfies `(d-1)^2 < n ∧ n < (d+1)^2`.

22. **`isqrt_is_sqrt`:** Main theorem. Statement:
    ```
    theorem isqrt_is_sqrt (n : ℤ) (hn : 0 ≤ n) :
      let a := isqrt n
      a ^ 2 ≤ n ∧ n < (a + 1) ^ 2
    ```

### Phase 7: Verification

23. Run `lake build` — must compile without errors
24. Add `#eval isqrt 0`, `#eval isqrt 1`, `#eval isqrt 100`, `#eval isqrt 1000000` sanity checks
25. Optionally add `#check @isqrt_is_sqrt` to confirm the theorem statement

## Relevant files

- `proofs/isqrt/src/isqrt.lean` — the existing Lean 3 proof (780 lines); kept as-is for reference
- `proofs/isqrt/leanpkg.toml` — Lean 3 project config; kept as-is
- `proofs/isqrt_lean4/` — new Lean 4 project (to be created)
- `snippets/isqrt.py` — the Python implementations (reference, not modified)

## Key patterns/functions to reuse from the Lean 3 proof

- The overall proof structure (helper lemmas → key_isqrt_lemma → isqrt_aux_correctness → isqrt_is_sqrt)
- The `section induction_step` pattern with parameters
- The informal proof in the comments (lines 44–140) — the mathematical argument is unchanged

## Risks and considerations

1. **Nat ↔ Int boundary:** Everything is `ℤ` at the surface, but `Nat.size` (or `Nat.log2`) works on `ℕ` internally. Coercions via `n.toNat` are needed at that boundary. Well-founded recursion on `c : ℤ` requires showing `c / 2 < c` for `c > 0` and using a measure like `Int.toNat c`.

2. **Division semantics:** Python `//` is floor division. We use `Int.fdiv` (not `Int.ediv`/`Int.div`, which truncate toward zero). Need to verify that Lean 4's `Int.fdiv` lemma library is sufficient. For positive operands they all agree, so this mainly matters if we ever generalize.

3. **`Nat.size` availability:** `Nat.size` is in `Mathlib.Data.Nat.Bits` (somewhat legacy). Alternative: use `Nat.log2` from core or `Nat.bitLength`. Need to check which has the best lemma support.
