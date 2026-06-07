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
import Mathlib.Data.Int.DivMod
import Isqrt.FDivLemmas

/-! ## Definitions -/

/-- Python's `a // b` (floor division). Uses `Int.fdiv`, which rounds toward
negative infinity — matching Python's `//` for all sign combinations.
Note: this is NOT `Int.ediv` (Lean's default `/` on `ℤ`). -/
def pyFloordiv (a b : ℤ) (_hb : b ≠ 0 := by omega) : ℤ := Int.fdiv a b

/-- Python's `n >> k` (right shift by `k` bits). Equivalent to floor division
by `2^k`. Requires a proof that the shift amount is nonneg. -/
def pyRshift (n k : ℤ) (_hk : 0 ≤ k := by omega) : ℤ := Int.fdiv n (2 ^ k.toNat)

/-- Python's `n << k` (left shift by `k` bits). Equivalent to multiplication
by `2^k`. Requires a proof that the shift amount is nonneg. -/
def pyLshift (n k : ℤ) (_hk : 0 ≤ k := by omega) : ℤ := n * (2 ^ k.toNat)

/-- Bit length of a natural number: the number of bits needed to represent `n`,
with `natBitLength 0 = 0`. Equivalent to `Nat.size`; defined via `Nat.log2`
for access to core Lean 4's `log2` lemma library. -/
def natBitLength : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.log2 (n + 1) + 1

/-- Python's `n.bit_length()`. Returns the number of bits needed to represent
`abs(n)`, with `(0).bit_length() == 0`. -/
def pyBitLength (n : ℤ) : ℤ := ↑(natBitLength n.natAbs)

/-! ## Python-style operators

These give `pyFloordiv`, `pyRshift`, and `pyLshift` the same syntax as
Python's `//`, `>>`, and `<<`, with relative precedence matching Python:
`py//` (70, same as `*`) binds tighter than `+` (65), which binds tighter
than `py>>` and `py<<` (60). -/

infixl:70 " py// " => pyFloordiv
infixl:60 " py>> " => pyRshift
infixl:60 " py<< " => pyLshift

/-! ## Unfolding lemmas

These reduce our Python-facing definitions to their underlying Lean
implementations, enabling use of Mathlib's `Int.fdiv` lemma library
and core's `Nat.log2` lemma library. -/

@[simp]
theorem pyFloordiv_def (a b : ℤ) (hb : b ≠ 0) :
    pyFloordiv a b hb = Int.fdiv a b := rfl

@[simp]
theorem pyRshift_def (n k : ℤ) (hk : 0 ≤ k) :
    pyRshift n k hk = Int.fdiv n (2 ^ k.toNat) := rfl

@[simp]
theorem pyLshift_def (n k : ℤ) (hk : 0 ≤ k) :
    pyLshift n k hk = n * 2 ^ k.toNat := rfl

@[simp]
theorem pyBitLength_def (n : ℤ) :
    pyBitLength n = ↑(natBitLength n.natAbs) := rfl

/-! ## Nonnegativity lemmas -/

/-- Floor division of a nonneg numerator by a positive denominator is nonneg. -/
theorem pyFloordiv_nonneg {a b : ℤ} {hb : b ≠ 0} (ha : 0 ≤ a) (hb_pos : 0 < b) :
    0 ≤ pyFloordiv a b hb := by
  simp only [pyFloordiv_def]; exact Int.fdiv_nonneg ha (le_of_lt hb_pos)

/-- Right-shifting a nonneg integer gives a nonneg result. -/
theorem pyRshift_nonneg {n k : ℤ} {hk : 0 ≤ k} (hn : 0 ≤ n) :
    0 ≤ pyRshift n k hk := by
  simp only [pyRshift_def]; exact Int.fdiv_nonneg hn (by positivity)

/-! ## Ordering and arithmetic lemmas

These bridge the Python operators to the `Int.fdiv` lemma library, so that
downstream code (notably `Iterative.lean`) can reason about `py>>` and `py//`
without ever mentioning `Int.fdiv` directly. -/

/-- Right-shifting a nonneg integer cannot increase it. -/
theorem pyRshift_le_self {n k : ℤ} (hn : 0 ≤ n) (hk : 0 ≤ k) :
    n py>> k ≤ n := by
  simp only [pyRshift_def]
  exact Int.fdiv_le_self_of_nonneg hn (by positivity)

/-- One more bit of right shift is a further floor-halving:
`n >> (k + 1) = (n >> k) // 2`. (This is the body's `e = d // 2` link — the
recursion's `c ↦ c // 2` step. No sign hypothesis on `n` is needed.) -/
theorem pyRshift_succ (n k : ℤ) (hk : 0 ≤ k) :
    n py>> (k + 1) = (n py>> k) py// 2 := by
  simp only [pyRshift_def, pyFloordiv_def]
  rw [show (k + 1).toNat = k.toNat + 1 from by omega, pow_succ,
      ← Int.fdiv_fdiv_eq_fdiv_mul n (by positivity) (by norm_num)]

/-- `(a // b) * b ≤ a` for positive divisor `b`. -/
theorem pyFloordiv_mul_le_self (a b : ℤ) (hb : 0 < b) :
    (a py// b) * b ≤ a := by
  simp only [pyFloordiv_def]
  exact Int.fdiv_mul_le_self hb
