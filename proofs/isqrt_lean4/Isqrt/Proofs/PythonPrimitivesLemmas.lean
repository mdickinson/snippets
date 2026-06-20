/-
Lemmas about the Python-operation mirrors of `Isqrt.Definitions.PythonPrimitives`
that the correctness proofs consume. Two groups, both stated in pure `Int.fdiv` /
`2 ^ ·` form (no Python operators), so the proofs build on them directly.

**Value extraction.** On its non-raising branch each of `pyFloordiv`, `pyLshift`,
`pyRshift` returns `.ok` of the corresponding `Int.fdiv` / power-of-two value. The
`_eq_ok` lemmas (with `Except.ok_bind`) are the bridges the proofs use to step through
the `do`-block once the side conditions (nonzero divisor, nonneg shift) are discharged.

**Bit length.** The power-of-two and floor-division facts about `int.bit_length()`.
The public `Int.bitLength` inlines its bit-length computation; this file re-declares it
as the ℕ-level `natBitLength` — kept honest by `Int.bitLength_natCast` — and connects it,
via `Nat.log2`, to power-of-two bounds, the per-step halving of a right shift, and the
loop-body left-shift nonnegativity fact.
-/

module

meta import Mathlib.Tactic.Positivity
public import Isqrt.Definitions.PythonPrimitives
import Isqrt.Proofs.FDivLemmas

public section

/-! ## Value extraction: the `Except`-returning operations -/

/-- For a nonzero divisor, `pyFloordiv` takes its `.ok` branch. -/
theorem pyFloordiv_eq_ok {a b : Int} (hb : b ≠ 0) :
    pyFloordiv a b = .ok (Int.fdiv a b) := by
  unfold pyFloordiv; split
  · omega
  · rfl

/-- For a nonneg shift count, `pyLshift` takes its `.ok` branch. The native
`<<<` is `· * 2 ^ ·` by core's `Int.shiftLeft_eq`. -/
theorem pyLshift_eq_ok {n k : Int} (hk : 0 ≤ k) :
    pyLshift n k = .ok (n * 2 ^ k.toNat) := by
  unfold pyLshift; split
  · omega
  · show (Except.ok (n <<< k.toNat) : PyExcept Int) = .ok (n * 2 ^ k.toNat)
    rw [Int.shiftLeft_eq]

/-- For a nonneg shift count, `pyRshift` takes its `.ok` branch. The native
`>>>` is the arithmetic (floor) shift `Int.fdiv · (2 ^ ·)`: core's
`Int.shiftRight_eq_div_pow` gives `· / 2 ^ ·`, which is `Int.fdiv` for the
positive divisor `2 ^ k.toNat` (`Int.fdiv_eq_ediv_of_nonneg`). -/
theorem pyRshift_eq_ok {n k : Int} (hk : 0 ≤ k) :
    pyRshift n k = .ok (Int.fdiv n (2 ^ k.toNat)) := by
  unfold pyRshift; split
  · omega
  · show (Except.ok (n >>> k.toNat) : PyExcept Int) = .ok (Int.fdiv n (2 ^ k.toNat))
    have h2 : (0 : Int) ≤ 2 ^ k.toNat := by positivity
    rw [Int.shiftRight_eq_div_pow, Int.fdiv_eq_ediv_of_nonneg n h2]
    norm_cast

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
surface: the public `Int.bitLength` (`Isqrt.Definitions.PythonPrimitives`) computes the same
bit length, and `Int.bitLength_natCast` below verifies — by a one-line `cases` — that
the two agree, so this re-declaration cannot silently drift from it. -/
def natBitLength (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-! ## Int.bitLength: defining-equation lemmas -/

/-- `Int.bitLength` of a `ℕ`-cast drops the `natAbs`: `(↑m : ℤ).bitLength = ↑(natBitLength m)`.
This is the bridge tying the trust-surface `Int.bitLength` to the named `natBitLength` above:
`cases m <;> rfl` checks they agree on each constructor — splitting `m` lets the `n = 0`
conditional reduce — so the re-declaration cannot silently drift. It's also the
form the ℤ↔ℕ bridges below (and in `Isqrt.Proofs.SizeConditions`) `rw` with directly;
the general `Int.bitLength_def` is the `@[simp]` normal form, so this one isn't `@[simp]`. -/
theorem Int.bitLength_natCast (m : ℕ) : (↑m : ℤ).bitLength = ↑(natBitLength m) := by
  cases m <;> rfl

/-- `Int.bitLength` unfolds to `natBitLength` on the underlying `natAbs`. Generalises
`Int.bitLength_natCast` from a `ℕ`-cast to any `n : ℤ`: both sides depend on `n` only
through `n.natAbs` (and `Int.bitLength`'s `n = 0` guard agrees with `n.natAbs = 0`). -/
@[simp]
theorem Int.bitLength_def (n : ℤ) : n.bitLength = ↑(natBitLength n.natAbs) := by
  rw [← Int.bitLength_natCast]
  unfold Int.bitLength
  simp [Int.natAbs_abs]

/-- `.toNat` of `Int.bitLength_natCast`: `((↑m : ℤ).bitLength).toNat = natBitLength m`. Not
`@[simp]` (simp derives it from `Int.bitLength_def` + casts); kept as a named target for
the *targeted* `rw`s below that must not disturb neighbouring casts. -/
theorem Int.toNat_bitLength_natCast (m : ℕ) :
    ((↑m : ℤ).bitLength).toNat = natBitLength m := by
  rw [Int.bitLength_natCast, Int.toNat_natCast]

/-! ## natBitLength: basic properties -/

theorem natBitLength_eq_zero_iff {n : ℕ} : natBitLength n = 0 ↔ n = 0 := by
  by_cases h : n = 0 <;> simp [natBitLength, h]

theorem natBitLength_pos_iff {n : ℕ} : 0 < natBitLength n ↔ 0 < n := by
  rw [Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero]
  exact not_congr natBitLength_eq_zero_iff

/-! ## natBitLength: power-of-two bounds -/

/-- Upper bound: `n < 2 ^ (natBitLength n)` for all `n`. -/
theorem lt_two_pow_natBitLength (n : ℕ) : n < 2 ^ natBitLength n := by
  by_cases h : n = 0
  · subst h; simp [natBitLength]
  · simp only [natBitLength, if_neg h]; exact Nat.lt_log2_self

/-- Lower bound: `2 ^ (natBitLength n - 1) ≤ n` when `n > 0`. -/
theorem two_pow_pred_natBitLength_le {n : ℕ} (hn : 0 < n) :
    2 ^ (natBitLength n - 1) ≤ n := by
  simp only [natBitLength, if_neg (by omega : ¬ n = 0), Nat.add_sub_cancel]
  exact Nat.log2_self_le (by omega)

/-! ## natBitLength: iff characterizations -/

/-- `natBitLength n ≤ k ↔ n < 2^k`. -/
theorem natBitLength_le_iff {n k : ℕ} : natBitLength n ≤ k ↔ n < 2 ^ k := by
  by_cases h : n = 0
  · subst h; exact iff_of_true (Nat.zero_le k) (by positivity)
  · simp only [natBitLength, if_neg h, Nat.add_one_le_iff]; exact Nat.log2_lt h

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
  -- peel one factor of two off a positive power
  have two_pow_pred : ∀ m, 1 ≤ m → (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) :=
    fun m hm => by rw [← pow_succ']; congr 1; omega
  apply le_antisymm
  · -- `natBitLength (n/2) ≤ natBitLength n - 1`  ⟺  `n/2 < 2^(natBitLength n - 1)`
    rw [natBitLength_le_iff]
    have hub := lt_two_pow_natBitLength n
    have hsplit := two_pow_pred (natBitLength n) hb
    omega
  · -- `natBitLength n - 1 ≤ natBitLength (n/2)`
    by_cases h1 : 2 ≤ natBitLength n
    · -- `natBitLength n ≥ 2`: from `2^(natBitLength n - 1) ≤ n` deduce `2^(b-2) ≤ n/2`.
      have hlow := two_pow_pred_natBitLength_le hn
      have hsplit := two_pow_pred (natBitLength n - 1) (by omega)
      rw [hsplit] at hlow
      have hhalf : 2 ^ (natBitLength n - 1 - 1) ≤ n / 2 := by omega
      have := (lt_natBitLength_iff (n := n / 2) (k := natBitLength n - 1 - 1)).mpr hhalf
      omega
    · -- `natBitLength n = 1`: the bound is `0 ≤ _`.
      omega

/-! ## Int.bitLength: ℤ-level properties -/

theorem Int.bitLength_nonneg (n : ℤ) : 0 ≤ n.bitLength := by
  rw [Int.bitLength_def]; positivity

theorem Int.bitLength_eq_zero_iff {n : ℤ} : n.bitLength = 0 ↔ n = 0 := by
  simp [natBitLength_eq_zero_iff, Int.natAbs_eq_zero]

theorem Int.bitLength_pos {n : ℤ} (hn : n ≠ 0) : 0 < n.bitLength := by
  rcases eq_or_lt_of_le (Int.bitLength_nonneg n) with h | h
  · exact absurd (Int.bitLength_eq_zero_iff.mp h.symm) hn
  · exact h

/-! ## Int.bitLength: interaction with floor-halving

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
theorem one_le_fdiv_two_pow_of_lt_bitLength {c s : ℤ}
    (hc : 0 ≤ c) (hs_nn : 0 ≤ s) (hs_lt : s < c.bitLength) :
    1 ≤ Int.fdiv c (2 ^ s.toNat) := by
  rw [Int.le_fdiv_iff_mul_le (by positivity), one_mul]
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc
  rw [Int.bitLength_natCast] at hs_lt
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
theorem fdiv_two_pow_bitLength_eq_zero {c : ℤ} (hc : 0 ≤ c) :
    Int.fdiv c (2 ^ c.bitLength.toNat) = 0 := by
  apply Int.fdiv_eq_zero_of_lt hc
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc
  rw [Int.toNat_bitLength_natCast]
  exact_mod_cast lt_two_pow_natBitLength cn

/-- Each recursive `c ↦ c // 2` step drops exactly one from `c.bit_length()`
(for `0 < c`). The ℤ counterpart of `natBitLength_div_two`, in the `.toNat`
form the structural-counter induction consumes. -/
theorem toNat_bitLength_fdiv_two {c : ℤ} (hc : 0 < c) :
    (Int.fdiv c 2).bitLength.toNat = c.bitLength.toNat - 1 := by
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc.le
  have hcn : 0 < cn := by exact_mod_cast hc
  have h_half : Int.fdiv (↑cn : ℤ) 2 = ((cn / 2 : ℕ) : ℤ) := by
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, Int.fdiv_natCast_natCast]
  -- Both bit-lengths reduce to `natBitLength` on the underlying ℕ (via the targeted
  -- `Int.toNat_bitLength_natCast`, which leaves the `cn / 2` cast untouched).
  rw [h_half, Int.toNat_bitLength_natCast, Int.toNat_bitLength_natCast, natBitLength_div_two hcn]

/-! ## Loop-body left-shift nonnegativity

The iterative isqrt recomputes, at loop position `s`, the shifts `d' = ⌊c/2^s⌋`
(new) and `d = ⌊c/2^(s+1)⌋` (the previous iteration's `d`), then forms the
left-shift amount `d' - d - 1`. This lemma shows it is nonneg, in pure `Int.fdiv`
form. -/

/-- The left-shift amount `⌊c/2^s⌋ - d - 1` is nonneg, where `d = ⌊c/2^(s+1)⌋`,
for `0 ≤ s < c.bit_length()`. The body's hardest precondition: it needs
`⌊c/2^s⌋ ≥ 1` (from `s < c.bit_length()`, `one_le_fdiv_two_pow_of_lt_bitLength`)
and the halving link `d = ⌊⌊c/2^s⌋/2⌋` (`fdiv_two_pow_succ`). -/
theorem fdiv_two_pow_lshift_nonneg {c s d : ℤ} (hc : 0 ≤ c) (hs_nn : 0 ≤ s)
    (hs_lt : s < c.bitLength) (hd : d = Int.fdiv c (2 ^ (s + 1).toNat)) :
    0 ≤ Int.fdiv c (2 ^ s.toNat) - d - 1 := by
  have hhalve : d = Int.fdiv (Int.fdiv c (2 ^ s.toNat)) 2 := by
    rw [hd]; exact fdiv_two_pow_succ c s hs_nn
  have hge1 : 1 ≤ Int.fdiv c (2 ^ s.toNat) :=
    one_le_fdiv_two_pow_of_lt_bitLength hc hs_nn hs_lt
  have hmul : Int.fdiv (Int.fdiv c (2 ^ s.toNat)) 2 * 2 ≤ Int.fdiv c (2 ^ s.toNat) :=
    Int.fdiv_mul_le_self (by norm_num)
  have hnn : 0 ≤ Int.fdiv (Int.fdiv c (2 ^ s.toNat)) 2 :=
    Int.fdiv_nonneg (by omega) (by norm_num)
  rw [hhalve]; omega

end
