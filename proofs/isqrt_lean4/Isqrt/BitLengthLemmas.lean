/-
Lemmas about `natBitLength` and `pyBitLength` needed for the isqrt proof.

These connect our `natBitLength` definition (via `Nat.log2`) to
power-of-two bounds, providing the ℕ and ℤ infrastructure for
reasoning about Python's `int.bit_length()`.
-/

import Isqrt.PythonOps

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
  simp [pyBitLength]

theorem pyBitLength_eq_zero_iff {n : ℤ} : pyBitLength n = 0 ↔ n = 0 := by
  simp [pyBitLength, natBitLength_eq_zero_iff, Int.natAbs_eq_zero]

theorem pyBitLength_pos {n : ℤ} (hn : n ≠ 0) : 0 < pyBitLength n := by
  rcases eq_or_lt_of_le (pyBitLength_nonneg n) with h | h
  · exact absurd (pyBitLength_eq_zero_iff.mp h.symm) hn
  · exact h

/-! ## pyBitLength: interaction with right shift -/

/-- For `0 ≤ s < c.bit_length()`, the right shift `c >> s` is at least `1`: it
still retains the leading bit. (Used to show the body's left-shift amount is
nonneg.) -/
theorem one_le_pyRshift_of_lt_pyBitLength {c s : ℤ}
    (hc : 0 ≤ c) (hs_nn : 0 ≤ s) (hs_lt : s < pyBitLength c) :
    1 ≤ c py>> s := by
  simp only [pyRshift_def]
  rw [Int.le_fdiv_iff_mul_le (by positivity), one_mul]
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc
  rw [show pyBitLength (↑cn : ℤ) = ↑(natBitLength cn) from by
        simp [pyBitLength]] at hs_lt
  have hbl_pos : 0 < natBitLength cn := by omega
  have hcn_pos : 0 < cn := natBitLength_pos_iff.mp hbl_pos
  have hbound : 2 ^ (natBitLength cn - 1) ≤ cn := two_pow_pred_natBitLength_le hcn_pos
  have hexp : s.toNat ≤ natBitLength cn - 1 := by omega
  calc (2 : ℤ) ^ s.toNat
      ≤ (2 : ℤ) ^ (natBitLength cn - 1) := by
        apply pow_le_pow_right₀ (by norm_num) hexp
    _ = ((2 ^ (natBitLength cn - 1) : ℕ) : ℤ) := by push_cast; rfl
    _ ≤ (↑cn : ℤ) := by exact_mod_cast hbound

/-- Right-shifting `c` by its own bit length yields `0` (since
`c < 2 ^ c.bit_length()`). This is the loop's seed value of `d`. -/
theorem pyRshift_pyBitLength_eq_zero {c : ℤ} (hc : 0 ≤ c) :
    pyRshift c (pyBitLength c) (pyBitLength_nonneg c) = 0 := by
  simp only [pyRshift_def]
  rw [Int.fdiv_eq_ediv_of_nonneg c (by positivity)]
  apply Int.ediv_eq_zero_of_lt hc
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc
  have hbl : (pyBitLength (↑cn : ℤ)).toNat = natBitLength cn := by
    rw [show pyBitLength (↑cn : ℤ) = ↑(natBitLength cn) from by
          simp [pyBitLength]]
    exact Int.toNat_natCast _
  rw [hbl]
  exact_mod_cast lt_two_pow_natBitLength cn

/-- Each recursive `c ↦ c // 2` step drops exactly one from `c.bit_length()`
(for `0 < c`). The ℤ counterpart of `natBitLength_div_two`, in the `.toNat`
form the structural-counter induction consumes. -/
theorem toNat_pyBitLength_pyFloordiv_two {c : ℤ} (hc : 0 < c) :
    (pyBitLength (c py// 2)).toNat = (pyBitLength c).toNat - 1 := by
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc.le
  have hcn : 0 < cn := by exact_mod_cast hc
  have h_half : (↑cn : ℤ) py// 2 = ((cn / 2 : ℕ) : ℤ) := by
    show Int.fdiv (↑cn : ℤ) 2 = _
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl,
        Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg _)]
    rfl
  rw [h_half]
  -- Both bit-lengths reduce to `natBitLength` on the underlying ℕ (introduce a
  -- fresh `↑m` so `simp` can't rewrite a cast-of-division).
  have key : ∀ m : ℕ, (pyBitLength (↑m : ℤ)).toNat = natBitLength m := fun m => by
    rw [show pyBitLength (↑m : ℤ) = ↑(natBitLength m) from by simp [pyBitLength]]
    exact Int.toNat_natCast _
  rw [key (cn / 2), key cn, natBitLength_div_two hcn]
