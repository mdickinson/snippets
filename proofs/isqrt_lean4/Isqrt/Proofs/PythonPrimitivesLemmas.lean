/-
Lemmas about the Python-operation mirrors of `Isqrt.Definitions.PythonPrimitives`
that the correctness proofs consume. Two groups, both stated in pure `Int.fdiv` /
`2 ^ ·` form (no Python operators), so the proofs build on them directly.

**Value extraction.** On its non-raising branch each of `pyFloordiv`, `pyLshift`,
`pyRshift` returns `.ok` of the corresponding `Int.fdiv` / power-of-two value. The
`_eq_ok` lemmas (with `Except.ok_bind`) are the bridges the proofs use to step through
the `do`-block once the side conditions (nonzero divisor, nonneg shift) are discharged.

**Bit length.** The power-of-two and floor-division facts about `int.bit_length()`.
The public `pyBitLength` inlines its bit-length computation; this file re-declares it
as the ℕ-level `natBitLength` — kept honest by `pyBitLength_natCast` — and connects it,
via `Nat.log2`, to power-of-two bounds, the per-step halving of a right shift, and the
two loop-body shift-amount nonnegativity facts.
-/

import Mathlib.Tactic.Positivity
import Isqrt.Definitions.PythonPrimitives
import Isqrt.Proofs.FDivLemmas

/-! ## Value extraction: the `Except`-returning operations -/

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

/-- `Except.ok a >>= f = f a` (definitional). The companion to the `_eq_ok`
lemmas above: once one of them rewrites an operation to `.ok v`, this steps the
`do`-block past the resulting bind. It's the `.ok`-form analogue of `pure_bind`,
which `simp` won't fire on a literal `Except.ok` (the head it sees is `Except.ok`,
not `pure`). Both correctness proofs use it. -/
theorem Except.ok_bind {ε α β : Type _} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-! ## natBitLength: the ℕ-level bit length -/

/-- Bit length of a natural number: the number of bits needed to represent `n`,
with `natBitLength 0 = 0`. Equivalent to `Nat.size`; defined via `Nat.log2` for
access to core Lean 4's `log2` lemma library.

This is the ℕ-level workhorse the bit-length proofs run on. It is *not* trust
surface: the public `pyBitLength` (`Isqrt.Definitions.PythonPrimitives`) inlines this same
computation, and `pyBitLength_natCast` below verifies — by a one-line `cases` — that
the two agree, so this re-declaration cannot silently drift from it. -/
def natBitLength : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.log2 (n + 1) + 1

/-! ## pyBitLength: defining-equation lemmas -/

/-- `pyBitLength` of a `ℕ`-cast drops the `natAbs`: `pyBitLength ↑m = ↑(natBitLength m)`.
This is the bridge tying the trust-surface `pyBitLength` (whose inlined bit-length match
is a distinct match-auxiliary) to the named `natBitLength` above: `cases m <;> rfl` checks
they agree on each constructor, so the re-declaration cannot silently drift. It's also the
form the ℤ↔ℕ bridges below (and in `Isqrt.Proofs.SizeConditions`) `rw` with directly;
the general `pyBitLength_def` is the `@[simp]` normal form, so this one isn't `@[simp]`. -/
theorem pyBitLength_natCast (m : ℕ) : pyBitLength (↑m : ℤ) = ↑(natBitLength m) := by
  cases m <;> rfl

/-- `pyBitLength` unfolds to `natBitLength` on the underlying `natAbs`. The general form
of `pyBitLength_natCast`, applied at `n.natAbs` — `pyBitLength` depends on `n` only through
`n.natAbs`, so the two are definitionally interchangeable. -/
@[simp]
theorem pyBitLength_def (n : ℤ) : pyBitLength n = ↑(natBitLength n.natAbs) :=
  pyBitLength_natCast n.natAbs

/-- `.toNat` of `pyBitLength_natCast`: `(pyBitLength ↑m).toNat = natBitLength m`. Not
`@[simp]` (simp derives it from `pyBitLength_def` + casts); kept as a named target for
the *targeted* `rw`s below that must not disturb neighbouring casts. -/
theorem toNat_pyBitLength_natCast (m : ℕ) :
    (pyBitLength (↑m : ℤ)).toNat = natBitLength m := by
  rw [pyBitLength_natCast, Int.toNat_natCast]

/-! ## natBitLength: basic properties -/

theorem natBitLength_eq_zero_iff {n : ℕ} : natBitLength n = 0 ↔ n = 0 := by
  cases n with
  | zero => simp [natBitLength]
  | succ n => simp [natBitLength]

theorem natBitLength_pos_iff {n : ℕ} : 0 < natBitLength n ↔ 0 < n := by
  rw [Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero]
  exact not_congr natBitLength_eq_zero_iff

/-! ## natBitLength: power-of-two bounds -/

/-- Upper bound: `n < 2 ^ (natBitLength n)` for all `n`. -/
theorem lt_two_pow_natBitLength (n : ℕ) : n < 2 ^ natBitLength n := by
  cases n with
  | zero => simp [natBitLength]
  | succ n =>
    simp only [natBitLength]
    exact Nat.lt_log2_self

/-- Lower bound: `2 ^ (natBitLength n - 1) ≤ n` when `n > 0`. -/
theorem two_pow_pred_natBitLength_le {n : ℕ} (hn : 0 < n) :
    2 ^ (natBitLength n - 1) ≤ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  simp only [natBitLength, Nat.add_sub_cancel]
  exact Nat.log2_self_le (Nat.succ_ne_zero m)

/-! ## natBitLength: iff characterizations -/

/-- `natBitLength n ≤ k ↔ n < 2^k`. -/
theorem natBitLength_le_iff {n k : ℕ} : natBitLength n ≤ k ↔ n < 2 ^ k := by
  cases n with
  | zero => simp [natBitLength]
  | succ n =>
    simp only [natBitLength]
    constructor
    · intro h
      have : Nat.log2 (n + 1) < k := by omega
      exact (Nat.log2_lt (Nat.succ_ne_zero n)).mp this
    · intro h
      have : Nat.log2 (n + 1) < k := (Nat.log2_lt (Nat.succ_ne_zero n)).mpr h
      omega

/-- `k < natBitLength n ↔ 2^k ≤ n`. Dual of `natBitLength_le_iff`. -/
theorem lt_natBitLength_iff {n k : ℕ} : k < natBitLength n ↔ 2 ^ k ≤ n := by
  rw [← not_iff_not]
  simp only [not_lt, not_le]
  exact natBitLength_le_iff

/-- Halving drops exactly one bit: `natBitLength (n / 2) = natBitLength n - 1`
for `0 < n`. This is the structural-counter linchpin — each recursive `c ↦ c // 2`
step decreases `c.bit_length()` by one, so a counter seeded at `c.bit_length()`
reaches `0` exactly when `c` does. -/
theorem natBitLength_div_two {n : ℕ} (hn : 0 < n) :
    natBitLength (n / 2) = natBitLength n - 1 := by
  have hb : 0 < natBitLength n := natBitLength_pos_iff.mpr hn
  apply le_antisymm
  · -- `natBitLength (n/2) ≤ natBitLength n - 1`  ⟺  `n/2 < 2^(natBitLength n - 1)`
    rw [natBitLength_le_iff]
    have hub := lt_two_pow_natBitLength n
    have hsplit : 2 ^ natBitLength n = 2 * 2 ^ (natBitLength n - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  · -- `natBitLength n - 1 ≤ natBitLength (n/2)`
    by_cases h1 : 2 ≤ natBitLength n
    · -- `natBitLength n ≥ 2`: from `2^(natBitLength n - 1) ≤ n` deduce `2^(b-2) ≤ n/2`.
      have hlow := two_pow_pred_natBitLength_le hn
      have hsplit : 2 ^ (natBitLength n - 1) = 2 * 2 ^ (natBitLength n - 2) := by
        rw [← pow_succ']; congr 1; omega
      rw [hsplit] at hlow
      have hhalf : 2 ^ (natBitLength n - 2) ≤ n / 2 := by omega
      have := (lt_natBitLength_iff (n := n / 2) (k := natBitLength n - 2)).mpr hhalf
      omega
    · -- `natBitLength n = 1`: the bound is `0 ≤ _`.
      omega

/-! ## pyBitLength: ℤ-level properties -/

theorem pyBitLength_nonneg (n : ℤ) : 0 ≤ pyBitLength n := by
  rw [pyBitLength_def]; positivity

theorem pyBitLength_eq_zero_iff {n : ℤ} : pyBitLength n = 0 ↔ n = 0 := by
  simp [natBitLength_eq_zero_iff, Int.natAbs_eq_zero]

theorem pyBitLength_pos {n : ℤ} (hn : n ≠ 0) : 0 < pyBitLength n := by
  rcases eq_or_lt_of_le (pyBitLength_nonneg n) with h | h
  · exact absurd (pyBitLength_eq_zero_iff.mp h.symm) hn
  · exact h

/-! ## pyBitLength: interaction with floor-halving

The right shift `c >> s` is the floor division `⌊c / 2^s⌋`; these lemmas are
stated directly on `Int.fdiv c (2 ^ s.toNat)` so they serve both the iterative and
recursive isqrt translations. -/

/-- One more step of floor-halving by a power of two:
`⌊c / 2^(s+1)⌋ = ⌊⌊c / 2^s⌋ / 2⌋`. The `Int.fdiv` twin of `pyRshift_succ` — the
recursion's `c ↦ c // 2` step. No sign hypothesis on `c` is needed. -/
theorem fdiv_two_pow_succ (c s : ℤ) (hs : 0 ≤ s) :
    Int.fdiv c (2 ^ (s + 1).toNat) = Int.fdiv (Int.fdiv c (2 ^ s.toNat)) 2 := by
  rw [show (s + 1).toNat = s.toNat + 1 from by omega, pow_succ,
      ← Int.fdiv_fdiv_eq_fdiv_mul c (by positivity) (by norm_num)]

/-- For `0 ≤ s < c.bit_length()`, the floor-halving `⌊c / 2^s⌋` is at least `1`:
it still retains the leading bit. (Used to show the body's left-shift amount is
nonneg.) -/
theorem one_le_fdiv_two_pow_of_lt_pyBitLength {c s : ℤ}
    (hc : 0 ≤ c) (hs_nn : 0 ≤ s) (hs_lt : s < pyBitLength c) :
    1 ≤ Int.fdiv c (2 ^ s.toNat) := by
  rw [Int.le_fdiv_iff_mul_le (by positivity), one_mul]
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc
  rw [pyBitLength_natCast] at hs_lt
  have hbl_pos : 0 < natBitLength cn := by omega
  have hcn_pos : 0 < cn := natBitLength_pos_iff.mp hbl_pos
  have hbound : 2 ^ (natBitLength cn - 1) ≤ cn := two_pow_pred_natBitLength_le hcn_pos
  have hexp : s.toNat ≤ natBitLength cn - 1 := by omega
  calc (2 : ℤ) ^ s.toNat
      ≤ (2 : ℤ) ^ (natBitLength cn - 1) := by
        apply pow_le_pow_right₀ (by norm_num) hexp
    _ = ((2 ^ (natBitLength cn - 1) : ℕ) : ℤ) := by push_cast; rfl
    _ ≤ (↑cn : ℤ) := by exact_mod_cast hbound

/-- Floor-halving `c` by `2 ^ c.bit_length()` yields `0` (since
`c < 2 ^ c.bit_length()`). This is the loop's seed value of `d`. -/
theorem fdiv_two_pow_pyBitLength_eq_zero {c : ℤ} (hc : 0 ≤ c) :
    Int.fdiv c (2 ^ (pyBitLength c).toNat) = 0 := by
  rw [Int.fdiv_eq_ediv_of_nonneg c (by positivity)]
  apply Int.ediv_eq_zero_of_lt hc
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc
  rw [toNat_pyBitLength_natCast]
  exact_mod_cast lt_two_pow_natBitLength cn

/-- Each recursive `c ↦ c // 2` step drops exactly one from `c.bit_length()`
(for `0 < c`). The ℤ counterpart of `natBitLength_div_two`, in the `.toNat`
form the structural-counter induction consumes. -/
theorem toNat_pyBitLength_fdiv_two {c : ℤ} (hc : 0 < c) :
    (pyBitLength (Int.fdiv c 2)).toNat = (pyBitLength c).toNat - 1 := by
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc.le
  have hcn : 0 < cn := by exact_mod_cast hc
  have h_half : Int.fdiv (↑cn : ℤ) 2 = ((cn / 2 : ℕ) : ℤ) := by
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, Int.fdiv_natCast_natCast]
  -- Both bit-lengths reduce to `natBitLength` on the underlying ℕ (via the targeted
  -- `toNat_pyBitLength_natCast`, which leaves the `cn / 2` cast untouched).
  rw [h_half, toNat_pyBitLength_natCast, toNat_pyBitLength_natCast, natBitLength_div_two hcn]

/-! ## Loop-body shift-amount nonnegativity

Both the iterative and recursive isqrt recompute, at loop position `s`, the shifts
`d' = ⌊c/2^s⌋` (new) and `d = ⌊c/2^(s+1)⌋` (the previous iteration's `d`), then form
the left-shift amount `d' - d - 1` and the right-shift amount `2c - d' - d + 1`.
These two lemmas show both are nonneg, in pure `Int.fdiv` form. -/

/-- The left-shift amount `⌊c/2^s⌋ - d - 1` is nonneg, where `d = ⌊c/2^(s+1)⌋`,
for `0 ≤ s < c.bit_length()`. The body's hardest precondition: it needs
`⌊c/2^s⌋ ≥ 1` (from `s < c.bit_length()`, `one_le_fdiv_two_pow_of_lt_pyBitLength`)
and the halving link `d = ⌊⌊c/2^s⌋/2⌋` (`fdiv_two_pow_succ`). -/
theorem fdiv_two_pow_lshift_nonneg {c s d : ℤ} (hc : 0 ≤ c) (hs_nn : 0 ≤ s)
    (hs_lt : s < pyBitLength c) (hd : d = Int.fdiv c (2 ^ (s + 1).toNat)) :
    0 ≤ Int.fdiv c (2 ^ s.toNat) - d - 1 := by
  have hhalve : d = Int.fdiv (Int.fdiv c (2 ^ s.toNat)) 2 := by
    rw [hd]; exact fdiv_two_pow_succ c s hs_nn
  have hge1 : 1 ≤ Int.fdiv c (2 ^ s.toNat) :=
    one_le_fdiv_two_pow_of_lt_pyBitLength hc hs_nn hs_lt
  have hmul : Int.fdiv (Int.fdiv c (2 ^ s.toNat)) 2 * 2 ≤ Int.fdiv c (2 ^ s.toNat) :=
    Int.fdiv_mul_le_self (by norm_num)
  have hnn : 0 ≤ Int.fdiv (Int.fdiv c (2 ^ s.toNat)) 2 :=
    Int.fdiv_nonneg (by omega) (by norm_num)
  rw [hhalve]; omega

/-- The right-shift amount `2c - ⌊c/2^s⌋ - d + 1` is nonneg, where
`d = ⌊c/2^(s+1)⌋`. Both floor-halvings are `≤ c` (for `0 ≤ c`), so the amount is
`≥ 1`. -/
theorem fdiv_two_pow_rshift_nonneg {c s d : ℤ} (hc : 0 ≤ c)
    (hd : d = Int.fdiv c (2 ^ (s + 1).toNat)) :
    0 ≤ 2 * c - Int.fdiv c (2 ^ s.toNat) - d + 1 := by
  have h1 : Int.fdiv c (2 ^ s.toNat) ≤ c := Int.fdiv_le_self_of_nonneg hc (by positivity)
  have h2 : Int.fdiv c (2 ^ (s + 1).toNat) ≤ c := Int.fdiv_le_self_of_nonneg hc (by positivity)
  rw [hd]; omega
