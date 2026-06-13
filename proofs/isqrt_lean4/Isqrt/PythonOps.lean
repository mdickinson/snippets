/-
Except-returning versions of the integer operations behind `math.isqrt`: floor
division `//`, right/left shift `>>`/`<<`, and the helper `range`.

Each operation that can raise in Python returns an `Except PyException`, carrying
either the result or the exception it would raise — `ZeroDivisionError` for `//`
by zero, `ValueError` for a negative shift count. This is the approach the README
calls "Option 2": the cost lands in the correctness proofs (`Isqrt.Correctness`,
`Isqrt.IterativeCorrectness`), which must show those error branches are never taken
for a nonnegative argument; the payoff is `do`-block translations of `isqrt`
(`Isqrt.Algorithm`, `Isqrt.Iterative`) that read almost verbatim like the CPython
source — every line that could raise in Python becomes a monadic bind `←`.

`pyBitLength` / `natBitLength` are *not* defined here — they cannot raise, so they
need no `Except` wrapper; they live in `Isqrt.BitLengthLemmas`, which the isqrt
translations import directly.
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
def pyFloordiv (a b : Int) : Except PyException Int :=
  if b = 0 then
    throw .zeroDivisionError
  else
    return Int.fdiv a b

/-- Python's `n << k` (left shift) as an `Except`: raises `ValueError` on a
negative shift count, otherwise returns `n * 2 ^ k`. -/
def pyLshift (n k : Int) : Except PyException Int :=
  if k < 0 then
    throw (.valueError "negative shift count")
  else
    return n * (2 ^ k.toNat)

/-- Python's `n >> k` (right shift) as an `Except`: raises `ValueError` on a
negative shift count, otherwise returns `Int.fdiv n (2 ^ k)` (floor division by
`2 ^ k`). -/
def pyRshift (n k : Int) : Except PyException Int :=
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
`Int.fdiv` / power-of-two value. These are the bridges the correctness proofs use
to step through the `do`-block once they have discharged the side conditions
(nonzero divisor, nonneg shift). Their right-hand sides mention only `Int.fdiv`
and powers of two, so the proofs can rewrite with them directly. -/

/-- For a nonzero divisor, `pyFloordiv` takes its `.ok` branch. -/
theorem pyFloordiv_eq_ok {a b : Int} (hb : b ≠ 0) :
    pyFloordiv a b = .ok (Int.fdiv a b) := by
  unfold pyFloordiv; split
  · omega
  · rfl

/-- For a nonneg shift count, `pyLshift` takes its `.ok` branch. -/
theorem pyLshift_eq_ok {n k : Int} (hk : 0 ≤ k) :
    pyLshift n k = .ok (n * 2 ^ k.toNat) := by
  unfold pyLshift; split
  · omega
  · rfl

/-- For a nonneg shift count, `pyRshift` takes its `.ok` branch. -/
theorem pyRshift_eq_ok {n k : Int} (hk : 0 ≤ k) :
    pyRshift n k = .ok (Int.fdiv n (2 ^ k.toNat)) := by
  unfold pyRshift; split
  · omega
  · rfl
