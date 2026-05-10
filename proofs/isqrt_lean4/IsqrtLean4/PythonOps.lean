/-
Python-compatible integer operations for use in Lean proofs.

Provides Lean definitions matching the semantics of Python's:
- `//` (floor division)
- `>>` (right shift)
- `<<` (left shift)
- `int.bit_length()`

Each operation that can raise an exception in Python requires a validity
proof at the call site (e.g., nonzero divisor, nonneg shift amount).
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! ## Definitions -/

/-- Python's `a // b` (floor division). Uses `Int.fdiv`, which rounds toward
negative infinity — matching Python's `//` for all sign combinations.
Note: this is NOT `Int.ediv` (Lean's default `/` on `ℤ`). -/
def pyFloorDiv (a b : ℤ) (_hb : b ≠ 0) : ℤ := Int.fdiv a b

/-- Python's `n >> k` (right shift by `k` bits). Equivalent to floor division
by `2^k`. Requires a proof that the shift amount is nonneg. -/
def pyRShift (n k : ℤ) (_hk : 0 ≤ k) : ℤ := Int.fdiv n (2 ^ k.toNat)

/-- Python's `n << k` (left shift by `k` bits). Equivalent to multiplication
by `2^k`. Requires a proof that the shift amount is nonneg. -/
def pyLShift (n k : ℤ) (_hk : 0 ≤ k) : ℤ := n * (2 ^ k.toNat)

/-- Bit length of a natural number: the number of bits needed to represent `n`,
with `natBitLength 0 = 0`. Equivalent to `Nat.size`; defined via `Nat.log2`
for access to core Lean 4's `log2` lemma library. -/
def natBitLength : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.log2 (n + 1) + 1

/-- Python's `n.bit_length()`. Returns the number of bits needed to represent
`abs(n)`, with `(0).bit_length() == 0`. -/
def pyBitLength (n : ℤ) : ℤ := ↑(natBitLength n.natAbs)

/-! ## Unfolding lemmas

These reduce our Python-facing definitions to their underlying Lean
implementations, enabling use of Mathlib's `Int.fdiv` lemma library
and core's `Nat.log2` lemma library. -/

@[simp]
theorem pyFloorDiv_def (a b : ℤ) (hb : b ≠ 0) :
    pyFloorDiv a b hb = Int.fdiv a b := rfl

@[simp]
theorem pyRShift_def (n k : ℤ) (hk : 0 ≤ k) :
    pyRShift n k hk = Int.fdiv n (2 ^ k.toNat) := rfl

@[simp]
theorem pyLShift_def (n k : ℤ) (hk : 0 ≤ k) :
    pyLShift n k hk = n * 2 ^ k.toNat := rfl

@[simp]
theorem pyBitLength_def (n : ℤ) :
    pyBitLength n = ↑(natBitLength n.natAbs) := rfl

theorem natBitLength_zero : natBitLength 0 = 0 := rfl

theorem natBitLength_succ (n : ℕ) :
    natBitLength (n + 1) = Nat.log2 (n + 1) + 1 := rfl

/-! ## Connection between shifts and floor division -/

/-- Right shift is a special case of floor division (by a power of 2). -/
theorem pyRShift_eq_pyFloorDiv (n k : ℤ) (hk : 0 ≤ k)
    (h : (2 : ℤ) ^ k.toNat ≠ 0) :
    pyRShift n k hk = pyFloorDiv n (2 ^ k.toNat) h := rfl

/-! ## Sanity checks -/

-- pyFloorDiv: positive denominator
#guard pyFloorDiv 7 2 (by omega) == 3
#guard pyFloorDiv (-7) 2 (by omega) == -4    -- floor division rounds toward -∞
#guard pyFloorDiv 0 3 (by omega) == 0

-- pyFloorDiv: negative denominator
#guard pyFloorDiv 7 (-2) (by omega) == -4    -- 7 // (-2) == -4 in Python
#guard pyFloorDiv (-7) (-2) (by omega) == 3  -- (-7) // (-2) == 3 in Python

-- pyRShift
#guard pyRShift 100 3 (by omega) == 12       -- 100 >> 3 == 100 // 8

-- pyLShift
#guard pyLShift 3 4 (by omega) == 48         -- 3 << 4 == 3 * 16

-- pyBitLength
#guard pyBitLength 0 == 0
#guard pyBitLength 1 == 1
#guard pyBitLength 255 == 8
#guard pyBitLength 256 == 9
#guard pyBitLength (-256) == 9               -- bit_length of abs
