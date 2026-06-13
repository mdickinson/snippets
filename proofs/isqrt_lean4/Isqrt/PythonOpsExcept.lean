/-
Except-returning ("Option 2") versions of the integer operations behind
`math.isqrt`: floor division `//`, right/left shift `>>`/`<<`, and the helper
`range`.

Where `Isqrt.PythonOps` models the operations that can raise (`//`, `>>`, `<<`)
as *proof-carrying* total functions — each call site discharges a side condition
(nonzero divisor, nonneg shift) — this module takes the other route the README
weighs ("Option 2"): each operation returns an `Except PyException`, carrying
either the result or the Python exception it would raise. The cost of that choice
lands in the correctness proof (`Isqrt.MonadicCorrectness`), which must show the
error branches are never taken; the upside is a `do`-block translation of `isqrt`
(`Isqrt.MonadicIsqrt`) that reads almost verbatim like the CPython source.

The names carry an `Except` suffix (`pyFloordivExcept`, …) so they coexist with
the proof-carrying `pyFloordiv`/`pyRshift`/`pyLshift` while both formulations live
in the tree; once the proof-carrying versions are retired the suffix is dropped.

`pyBitLength` / `natBitLength` are *not* redefined here — they cannot raise, so
they are shared unchanged from `Isqrt.PythonOps` (the `isqrt` translation pulls
them in via `Isqrt.BitLengthLemmas`).
-/

import Isqrt.FDivLemmas

/-- The Python exceptions that `math.isqrt` and the operations it uses can raise.
`deriving Repr` lets `#eval` print the exception's contents in tests (the analogue
of a Python `__repr__`). -/
inductive PyException where
  | zeroDivisionError
  | valueError (msg : String)
  deriving Repr

/-- Python's `a // b` (floor division) as an `Except`: raises `ZeroDivisionError`
when `b = 0`, otherwise returns `Int.fdiv a b` — which rounds toward `-∞`, matching
Python's `//` for every sign combination. -/
def pyFloordivExcept (a b : Int) : Except PyException Int :=
  if b = 0 then
    throw .zeroDivisionError
  else
    return Int.fdiv a b

/-- Python's `n << k` (left shift) as an `Except`: raises `ValueError` on a
negative shift count, otherwise returns `n * 2 ^ k`. -/
def pyLshiftExcept (n k : Int) : Except PyException Int :=
  if k < 0 then
    throw (.valueError "negative shift count")
  else
    return n * (2 ^ k.toNat)

/-- Python's `n >> k` (right shift) as an `Except`: raises `ValueError` on a
negative shift count, otherwise returns `Int.fdiv n (2 ^ k)` (floor division by
`2 ^ k`). -/
def pyRshiftExcept (n k : Int) : Except PyException Int :=
  if k < 0 then
    throw (.valueError "negative shift count")
  else
    return Int.fdiv n (2 ^ k.toNat)

/-- Python's single-argument `range(n)` as a list of `Int`s. `n.toNat` maps
negative `n` to `0`, exactly matching Python's "empty range, no error" behaviour
for nonpositive arguments. -/
def pyRange (n : Int) : List Int := (List.range n.toNat).map Int.ofNat

/-! ## Value-extraction lemmas

On its non-raising branch each operation returns `.ok` of the corresponding
`Int.fdiv` / power-of-two value. These are the bridges the correctness proof uses
to step through the `do`-block once it has discharged the side conditions. They
mention only `Int.fdiv` (never the proof-carrying `py>>`/`py//`), so they survive
the eventual retirement of `Isqrt.PythonOps` unchanged. -/

/-- For a nonzero divisor, `pyFloordivExcept` takes its `.ok` branch. -/
theorem pyFloordivExcept_eq_ok {a b : Int} (hb : b ≠ 0) :
    pyFloordivExcept a b = .ok (Int.fdiv a b) := by
  unfold pyFloordivExcept; split
  · omega
  · rfl

/-- For a nonneg shift count, `pyLshiftExcept` takes its `.ok` branch. -/
theorem pyLshiftExcept_eq_ok {n k : Int} (hk : 0 ≤ k) :
    pyLshiftExcept n k = .ok (n * 2 ^ k.toNat) := by
  unfold pyLshiftExcept; split
  · omega
  · rfl

/-- For a nonneg shift count, `pyRshiftExcept` takes its `.ok` branch. -/
theorem pyRshiftExcept_eq_ok {n k : Int} (hk : 0 ≤ k) :
    pyRshiftExcept n k = .ok (Int.fdiv n (2 ^ k.toNat)) := by
  unfold pyRshiftExcept; split
  · omega
  · rfl
