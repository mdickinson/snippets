/-
Lean mirrors of the Python operations and builtins behind `math.isqrt`: floor
division `//`, right/left shift `>>`/`<<`, the helper `range`, and
`int.bit_length()`. Part of the **definitions** layer — trust surface the reader
checks against Python.

Each operation that can raise in Python returns an `Except PyException`, carrying
either the result or the exception it would raise — `ZeroDivisionError` for `//`
by zero, `ValueError` for a negative shift count. This is the approach the README
calls "Option 2": the cost lands in the correctness proofs (`Isqrt.Proofs.RecursiveCorrectness`,
`Isqrt.Proofs.IterativeCorrectness`), which must show those error branches are never
taken for a nonnegative argument; the payoff is `do`-block translations of `isqrt`
(`Isqrt.Definitions.Recursive`, `Isqrt.Definitions.Iterative`) that read almost
verbatim like the CPython source — every line that could raise in Python becomes a
monadic bind `←`. The lemmas that step a `do`-block past these operations on their
non-raising branch live in `Isqrt.Proofs.PythonOpsLemmas`.

`pyBitLength` (`int.bit_length()`) sits here too, alongside the operations it
joins; unlike `//`/`>>`/`<<` it can't raise, so it needs no `Except` wrapper — just
a plain `Int`-valued function. Its supporting lemmas live in
`Isqrt.Proofs.BitLengthLemmas`.
-/

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

/-- Python's `n.bit_length()`. Returns the number of bits needed to represent
`abs(n)`, with `(0).bit_length() == 0`. Never raises, so — unlike `//`/`>>`/`<<` —
it needs no `Except` form: a single plain `Int`-valued function the iterative and
recursive isqrt translations share.

Computed via `Nat.log2` on `abs(n)` (`n.natAbs`), matching `bit_length`'s
`⌊log2 n⌋ + 1` for `n > 0`. The ℕ-level computation is re-stated as the named
`natBitLength` in `Isqrt.Proofs.BitLengthLemmas`, where the proofs reason about it;
`pyBitLength_natCast` there checks that the two agree. -/
def pyBitLength (n : Int) : Int :=
  ↑(match n.natAbs with
    | 0 => 0
    | m + 1 => Nat.log2 (m + 1) + 1)
