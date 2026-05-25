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

/-! ## natBitLength: interaction with division -/

/-- Right-shifting (dividing by `2^k`) reduces bit length by `k`. -/
theorem natBitLength_div_two_pow (n k : ℕ) :
    natBitLength (n / 2 ^ k) = natBitLength n - k := by
  by_cases hk : k ≤ natBitLength n
  · -- Case k ≤ natBitLength n
    apply Nat.le_antisymm
    · -- ≤: natBitLength (n / 2^k) ≤ natBitLength n - k
      rw [natBitLength_le_iff, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k),
          ← pow_add, Nat.sub_add_cancel hk]
      exact lt_two_pow_natBitLength n
    · -- ≥: natBitLength n - k ≤ natBitLength (n / 2^k)
      rcases Nat.eq_or_lt_of_le hk with rfl | hk'
      · simp
      · -- k < natBitLength n, so natBitLength n - k ≥ 1
        have hn : 0 < n := natBitLength_pos_iff.mp (by omega)
        suffices natBitLength n - k - 1 < natBitLength (n / 2 ^ k) by omega
        rw [lt_natBitLength_iff, Nat.le_div_iff_mul_le (Nat.two_pow_pos k),
            ← pow_add]
        have : natBitLength n - k - 1 + k = natBitLength n - 1 := by omega
        rw [this]
        exact two_pow_pred_natBitLength_le hn
  · -- Case k > natBitLength n: both sides are 0
    have hk' : natBitLength n ≤ k := by omega
    rw [Nat.sub_eq_zero_of_le hk', natBitLength_eq_zero_iff]
    exact Nat.div_eq_of_lt (natBitLength_le_iff.mp hk')

/-! ## pyBitLength: ℤ-level properties -/

theorem pyBitLength_nonneg (n : ℤ) : 0 ≤ pyBitLength n := by
  simp [pyBitLength]

theorem pyBitLength_eq_zero_iff {n : ℤ} : pyBitLength n = 0 ↔ n = 0 := by
  simp [pyBitLength, natBitLength_eq_zero_iff, Int.natAbs_eq_zero]

theorem pyBitLength_pos {n : ℤ} (hn : n ≠ 0) : 0 < pyBitLength n := by
  rcases eq_or_lt_of_le (pyBitLength_nonneg n) with h | h
  · exact absurd (pyBitLength_eq_zero_iff.mp h.symm) hn
  · exact h

theorem pyBitLength_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    pyBitLength n = ↑(natBitLength n.toNat) := by
  unfold pyBitLength
  congr 1
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rfl
