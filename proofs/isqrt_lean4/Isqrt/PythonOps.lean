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

-- `Ring` and `Linarith` are not used directly in this file; `Isqrt.Iterative`
-- calls `ring`/`linarith`/`nlinarith` without importing those tactics and relies
-- on this transitive re-export. Dropping them as "unused" breaks the downstream
-- build under `--wfail`. (The cleaner fix is to import the tactics in the files
-- that use them.)
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Int.DivMod
import Isqrt.FDivLemmas
import Isqrt.BitLengthLemmas

/-! ## Definitions -/

/-- Python's `a // b` (floor division). Uses `Int.fdiv`, which rounds toward
negative infinity — matching Python's `//` for all sign combinations.
Note: this is NOT `Int.ediv` (Lean's default `/` on `ℤ`). -/
@[nolint unusedArguments]
def pyFloordiv (a b : ℤ) (_hb : b ≠ 0 := by omega) : ℤ := Int.fdiv a b

/-- Python's `n >> k` (right shift by `k` bits). Equivalent to floor division
by `2^k`. Requires a proof that the shift amount is nonneg. -/
@[nolint unusedArguments]
def pyRshift (n k : ℤ) (_hk : 0 ≤ k := by omega) : ℤ := Int.fdiv n (2 ^ k.toNat)

/-- Python's `n << k` (left shift by `k` bits). Equivalent to multiplication
by `2^k`. Requires a proof that the shift amount is nonneg. -/
@[nolint unusedArguments]
def pyLshift (n k : ℤ) (_hk : 0 ≤ k := by omega) : ℤ := n * (2 ^ k.toNat)

/-! ## Python-style operators

These give `pyFloordiv`, `pyRshift`, and `pyLshift` the same syntax as
Python's `//`, `>>`, and `<<`, with relative precedence matching Python:
`py//` (70, same as `*`) binds tighter than `+` (65), which binds tighter
than `py>>` and `py<<` (60). -/

@[inherit_doc] infixl:70 " py// " => pyFloordiv
@[inherit_doc] infixl:60 " py>> " => pyRshift
@[inherit_doc] infixl:60 " py<< " => pyLshift

/-! ## Unfolding lemmas

These reduce our Python-facing definitions to their underlying Lean
implementations, enabling use of Mathlib's `Int.fdiv` lemma library
(and, via `natBitLength`, core's `Nat.log2` lemmas). -/

@[simp]
theorem pyFloordiv_def (a b : ℤ) (hb : b ≠ 0) :
    pyFloordiv a b hb = Int.fdiv a b := rfl

@[simp]
theorem pyRshift_def (n k : ℤ) (hk : 0 ≤ k) :
    pyRshift n k hk = Int.fdiv n (2 ^ k.toNat) := rfl

@[simp]
theorem pyLshift_def (n k : ℤ) (hk : 0 ≤ k) :
    pyLshift n k hk = n * 2 ^ k.toNat := rfl

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

/-- `(a << K) + (n >> J) // a` is positive when `a > 0`, `n ≥ 0`, and the shift
amounts are nonneg: the left shift of a positive is positive and the
floor-division term is nonneg. This is the shape of both the recursive
`isqrtAux` return and the iterative loop body's new `a`. -/
theorem pyLshift_add_pyFloordiv_pos {a n K J : ℤ}
    (ha : 0 < a) (hn : 0 ≤ n) (hK : 0 ≤ K) (hJ : 0 ≤ J) :
    0 < (a py<< K) + (n py>> J) py// a := by
  have h_shift_pos : 0 < a py<< K := by
    simp only [pyLshift_def]; exact mul_pos ha (by positivity)
  have h_div_nonneg : 0 ≤ (n py>> J) py// a := pyFloordiv_nonneg (pyRshift_nonneg hn) ha
  omega

/-! ## Bit-length interaction with right shift

`py>>`-form restatements of `Isqrt.BitLengthLemmas`'
`one_le_fdiv_two_pow_of_lt_pyBitLength` / `fdiv_two_pow_pyBitLength_eq_zero`, for the
proof-carrying isqrt. (The `Except` translation uses the `Int.fdiv` originals directly.) -/

/-- For `0 ≤ s < c.bit_length()`, the right shift `c >> s` is at least `1`: it still
retains the leading bit. (Used to show the body's left-shift amount is nonneg.) -/
theorem one_le_pyRshift_of_lt_pyBitLength {c s : ℤ}
    (hc : 0 ≤ c) (hs_nn : 0 ≤ s) (hs_lt : s < pyBitLength c) :
    1 ≤ c py>> s := by
  rw [pyRshift_def]; exact one_le_fdiv_two_pow_of_lt_pyBitLength hc hs_nn hs_lt

/-- Right-shifting `c` by its own bit length yields `0` (since `c < 2 ^ c.bit_length()`).
This is the loop's seed value of `d`. -/
theorem pyRshift_pyBitLength_eq_zero {c : ℤ} (hc : 0 ≤ c) :
    pyRshift c (pyBitLength c) (pyBitLength_nonneg c) = 0 := by
  rw [pyRshift_def]; exact fdiv_two_pow_pyBitLength_eq_zero hc
