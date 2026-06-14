/-
Bit length — the Lean mirror of Python's `int.bit_length()`. Part of the
**definitions** layer: this is trust surface (the reader checks it against
Python), so it holds only the definitions. Every lemma about them — power-of-two
bounds, per-step halving, shift-amount nonnegativity — lives in
`Isqrt.Proofs.BitLengthLemmas`.
-/

/-- Bit length of a natural number: the number of bits needed to represent `n`,
with `natBitLength 0 = 0`. Equivalent to `Nat.size`; defined via `Nat.log2`
for access to core Lean 4's `log2` lemma library. -/
def natBitLength : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.log2 (n + 1) + 1

/-- Python's `n.bit_length()`. Returns the number of bits needed to represent
`abs(n)`, with `(0).bit_length() == 0`. Never raises, so — unlike `//`/`>>`/`<<` —
it needs no `Except` form: a single plain `Int`-valued function the iterative and
recursive isqrt translations share. -/
def pyBitLength (n : Int) : Int := ↑(natBitLength n.natAbs)
