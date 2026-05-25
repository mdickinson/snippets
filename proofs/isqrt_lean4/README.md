# Correctness proof for CPython's `math.isqrt`

A formal proof in Lean 4 that the recursive integer square root algorithm
used by CPython's `math.isqrt` function is correct.

## Prerequisites

Install [elan](https://github.com/leanprover/elan) (the Lean version manager):

```
curl https://elan.dev/install.sh -sSf | sh
```

## Building

From this directory:

```
lake exe cache get   # download prebuilt Mathlib (avoids compiling from source)
lake build           # build the project
```

The first `lake` command you run will automatically download the correct
Lean toolchain version (specified in `lean-toolchain`).

Downloading the Mathlib cache (`lake exe cache get`) fetches ~1-2 GB of
prebuilt `.olean` files. Without this step, `lake build` would compile
all of Mathlib from source, which takes several hours.

## Project structure

```
lakefile.lean              -- project configuration and dependencies
lean-toolchain             -- Lean version pin
IsqrtLean4.lean            -- root module (imports everything)
IsqrtLean4/
  PythonOps.lean           -- Lean definitions matching Python's //, >>, <<, bit_length
  FDivLemmas.lean          -- Int.fdiv ordering lemmas and Int↔ℕ bridge
  BitLengthLemmas.lean     -- natBitLength / pyBitLength properties
  KeyLemma.lean            -- key algebraic lemma; isNearSqrt predicate
  SizeConditions.lean      -- size-condition invariants carried through the recursion
  Isqrt.lean               -- isqrt algorithm definition and correctness proof
  Tests/
    PythonOps.lean         -- #guard checks for the Python operations
    Isqrt.lean             -- #guard checks for isqrt on concrete values
```

## Related files

- `../isqrt/` — the original Lean 3 proof (kept for reference)
- `../../snippets/isqrt.py` — Python implementations of the algorithm
