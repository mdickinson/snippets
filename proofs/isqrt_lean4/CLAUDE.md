# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this project is

A Lean 4 + Mathlib 4 formalization of correctness for the **recursive** integer square root algorithm behind CPython's `math.isqrt`. The proof itself is finished (PR #16, all phases complete). Work here is typically maintenance, refactoring, or extending the prose docs.

The README explains the Python-to-Lean translation strategy and what a reader has to trust; `PLAN.md` records the design decisions made during the port from the Lean 3 predecessor in `../isqrt/`. Both are kept up to date with the code.

## Build commands

From this directory:

```
lake exe cache get   # one-time: download prebuilt Mathlib (~1-2 GB of .olean files)
lake build           # build library + tests
lake build --wfail   # also fail on warnings (matches CI)
```

Without `lake exe cache get`, `lake build` compiles Mathlib from source (hours). The `lean-toolchain` file pins the Lean version; `lake` downloads it on first use.

Both `Isqrt` (implementation) and `IsqrtTests` (`#guard` checks) are `@[default_target]`, so `lake build` runs the tests. There's no separate test runner — a `#guard` failure surfaces as a build error.

To rebuild a single module, edit it and re-run `lake build`; lake handles incremental compilation. There's no convention here for running a single `#guard` in isolation.

## Architecture

The library is split so dependencies flow one way: low-level Python-operator wrappers → arithmetic lemmas → the key algebraic lemma + size invariants → algorithm definitions → correctness. `Isqrt.lean` is the library root; `IsqrtTests.lean` imports `Tests/`; the implementation library does **not** import the tests.

Key modules (see `PLAN.md` for the full design rationale):

- `Isqrt/PythonOps.lean` — `pyFloordiv`, `pyRshift`, `pyLshift`, `pyBitLength`, and the `py//`, `py>>`, `py<<` operators. Each Python operator that can raise on bad input is a proof-carrying function: the precondition (`b ≠ 0`, `0 ≤ k`) is an argument with a `by omega` default. Operator precedences are engineered to match Python's. Also holds the operator-level ordering lemmas (`pyRshift_le_self`, `pyRshift_succ`, `pyFloordiv_mul_le_self`) that let code reason about `py>>`/`py//` without naming `Int.fdiv`; for these it `import`s `FDivLemmas` (acyclic — `FDivLemmas` names no py-op).
- `Isqrt/FDivLemmas.lean`, `Isqrt/BitLengthLemmas.lean` — arithmetic lemmas about `Int.fdiv` (Python's floor division) and `pyBitLength`. Thin wrappers over Mathlib + `Int.fdiv_eq_ediv_of_nonneg`. `FDivLemmas` is the foundational floor-division layer (imported by `PythonOps`); `BitLengthLemmas` also carries the py-op right-shift facts `one_le_pyRshift_of_lt_pyBitLength` and `pyRshift_pyBitLength_eq_zero`.
- `Isqrt/RecursionDepth.lean` — a one-lemma module holding `isqrt_c_nonneg` (the recursion depth `(n.bit_length() - 1) // 2` is nonneg for `n ≠ 0`). Shared by both `Algorithm.lean` and the iterative `Iterative.lean` so neither imports the other.
- `Isqrt/KeyLemma.lean` — `key_isqrt_lemma` and the `isNearSqrt a n := (a-1)² < n ∧ n < (a+1)²` predicate. The core algebraic step that justifies the recursion.
- `Isqrt/SizeConditions.lean` — the `hasSizeCondition c n := 4^c ≤ n < 4^(c+1)` invariant carried through the recursion. Hybrid `ℕ`/`ℤ` split: core lemmas at `ℕ`, integer corollaries bridge via `Int.eq_ofNat_of_zero_le`.
- `Isqrt/Algorithm.lean` — `isqrt_aux` and `isqrt`. `isqrt_aux` returns `{ a : ℤ // 0 < a }` so the `// a` division in the recursive case has a positivity proof to hand. Terminates on `c.toNat`.
- `Isqrt/Correctness.lean` — strong induction via `Nat.strong_induction_on` on `c.toNat`. The top-level theorem is `isqrt_is_sqrt`, stating `a * a ≤ n ∧ n < (a + 1) * (a + 1)` for `a := isqrt n hn`.

## Conventions specific to this project

- **`Int` everywhere, not `Nat`.** Python `int` is signed and arbitrary precision; the Lean 3 predecessor used `Nat` and paid a heavy tax in truncating-subtraction lemmas. Don't reintroduce `Nat` in public signatures — only as a local bridge (`.toNat`, `natBitLength`).
- **`Int.fdiv`, not `/` or `Int.ediv`.** Python's `//` rounds toward `-∞`; Lean's default `/` rounds toward zero. They agree on the inputs `isqrt` actually uses (nonneg ÷ positive) but `fdiv` is the faithful translation.
- **`if _ : c = 0 then ...`, not `if c == 0`.** The `Prop`-valued, dependent `if` is intentional: it threads `c = 0` / `c ≠ 0` proofs into the branches, which `omega` consumes directly. Don't "fix" this by switching to `==`.
- **Public statements mirror Python with `*`, not `^2`.** `isqrt_is_sqrt` uses `a * a ≤ n` because Python's `**` is type-unsafe; multiplicative form is preferred for statements that mirror Python source.
- **Naming.** `a` is the recursive result, `d` is the combined result, `M = 2^k`. Matches the informal proof; the Lean 3 formal proof swapped `a` and `d` — don't follow that here.
- **`by omega` is the default precondition tactic.** Exception: when a goal contains `n py>> (... py// ...)`, `omega` can't see through `py//` — spell out the proof inline using `pyFloordiv_nonneg`.

## Working style

- Apply review findings one at a time and run `lake build` after each. Don't blindly trust reviewer suggestions — `lake build` is the source of truth.
- README and `PLAN.md` are self-contained. They should be readable without depending on the wider `snippets` repo.
- Session-learned gotchas fold into `PLAN.md`, not separate handoff files.
