/-
The size condition and its descent. `SizedProblem` carries the bit-length form `isSizedAt n c`
(`0 < n ∧ c = (n.toNat.size - 1)/2`); the key lemma wants the power bound `hasSizeCondition n c`
(`4^c ≤ n < 4^(c+1)`). `hasSizeCondition_of_isSizedAt` bridges them, `size_condition_at_depth` /
`size_condition_step` descend the level, and `isSuitableScaler_of_hasSizeCondition` /
`isNearSquareRoot_one_of_hasSizeCondition` feed the key lemma's step and base cases.
-/

module

public import Isqrt.Proofs.KeyLemma
public import Isqrt.Proofs.SupportLemmas

public section

/-! ## Nat-level power bounds -/

/-- `4·M⁴ ≤ n` from the power bound's lower bound, where `M = 2^((c-1)/2)`. -/
private theorem M_bound_from_size_nat {c n : Nat} (hc : 0 < c) (h_lo : 4 ^ c ≤ n) :
    4 * (2 ^ ((c - 1) / 2)) ^ 4 ≤ n := by
  -- Below, k = ⌊(c-1)/2⌋ (spelled out in full).
  calc 4 * (2 ^ ((c - 1) / 2)) ^ 4
      = 2 ^ (4 * ((c - 1) / 2) + 2) := by
        rw [show (4 : Nat) = 2^2 from rfl, ← Nat.pow_mul, ← Nat.pow_add]
        congr 1; omega
    _ ≤ 2 ^ (2 * c) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 4 ^ c := by rw [show (4 : Nat) = 2^2 from rfl, ← Nat.pow_mul]
    _ ≤ n := h_lo

/-! ## The power bound `hasSizeCondition` -/

/-- The power bound: `4^c ≤ n < 4^(c+1)`. -/
@[expose] def hasSizeCondition (n : Int) (c : Nat) : Prop :=
  (4 : Int) ^ c ≤ n ∧ n < (4 : Int) ^ (c + 1)

/-- The power bound forces `0 < n` (since `1 ≤ 4^c ≤ n`). -/
theorem hasSizeCondition.pos {n : Int} {c : Nat} (h : hasSizeCondition n c) : 0 < n := by
  have h0 : (0 : Int) < 4 ^ c := Int.pow_pos (by omega)
  have h1 := h.1
  omega

/-- The power bound forces `0 ≤ n`. -/
private theorem hasSizeCondition.nonneg {n : Int} {c : Nat} (h : hasSizeCondition n c) : 0 ≤ n :=
  Int.le_of_lt h.pos

/-- For a `Nat`-cast value, the power bound is its `Nat`-level form. -/
private theorem hasSizeCondition_natCast_iff {n c : Nat} :
    hasSizeCondition (↑n) c ↔ 4 ^ c ≤ n ∧ n < 4 ^ (c + 1) := by
  unfold hasSizeCondition
  norm_cast

/-! ## The bit-length size condition `isSizedAt` -/

/-- The bit-length form of the size condition: `0 < n` and `c = (n.toNat.size - 1)/2`, the
algorithm's seed. -/
@[expose] def isSizedAt (n : Int) (c : Nat) : Prop :=
  0 < n ∧ c = (n.toNat.size - 1) / 2

/-- `isSizedAt` forces `0 < n` (by definition). -/
theorem isSizedAt.pos {n : Int} {c : Nat} (h : isSizedAt n c) : 0 < n := h.1

/-- The bit-length size condition implies the power bound: `isSizedAt n c → hasSizeCondition n c`. -/
theorem hasSizeCondition_of_isSizedAt {n : Int} {c : Nat} (h : isSizedAt n c) :
    hasSizeCondition n c := by
  obtain ⟨hpos, hc⟩ := h
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hpos)
  rw [Int.toNat_natCast] at hc
  rw [hasSizeCondition_natCast_iff, show 4 = 2 ^ 2 from rfl]
  simp only [← Nat.pow_mul]
  have hms : 0 < m.size := Nat.size_pos.mpr (by omega)
  constructor
  · apply Nat.le_of_not_lt; rw [←Nat.size_le]; omega
  · rw [←Nat.size_le]; omega

/-! ## Initial size condition -/

/-- `n` sits at its own level: `isSizedAt n ((n.toNat.size - 1)/2)`. -/
theorem size_condition_initial {n : Int} (hn : 0 < n) :
    isSizedAt n ((n.toNat.size - 1) / 2) := ⟨hn, rfl⟩

/-! ## Descent of the size condition -/

/-- Descent to any depth `d ≤ c`: right-shifting `isSizedAt n c` by `2(c-d)` gives
`isSizedAt (n >>> 2(c-d)) d`. -/
theorem size_condition_at_depth {n : Int} {c d : Nat} (hd_hi : d ≤ c) (h : isSizedAt n c) :
    isSizedAt (n >>> (2 * (c - d))) d := by
  obtain ⟨hpos, hc⟩ := h
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hpos)
  have hm_pos : 0 < m := by exact_mod_cast hpos
  rw [Int.toNat_natCast] at hc
  have hms : 0 < m.size := Nat.size_pos.mpr hm_pos
  have hk_le : 2 * (c - d) < m.size := by omega
  -- Push the Int shift down to the Nat shift, then read off positivity and the level.
  rw [← Int.natCast_shiftRight]
  refine ⟨?_, ?_⟩
  · exact_mod_cast Nat.shiftRight_pos hk_le
  · rw [Int.toNat_natCast, Nat.size_shiftRight]
    omega

/-- The recursive step `c ↦ ⌊c/2⌋`: right-shifting by `2⌊(c-1)/2⌋+2` lands the level at `c/2` (the
`d = ⌊c/2⌋` case of `size_condition_at_depth`). -/
theorem size_condition_step {n : Int} {c : Nat} (hc : 0 < c) (h : isSizedAt n c) :
    isSizedAt (n >>> (2 * ((c - 1) / 2) + 2)) (c / 2) := by
  rw [show 2 * ((c - 1) / 2) + 2 = 2 * (c - c / 2) from by omega]
  exact size_condition_at_depth (Nat.div_le_self c 2) h

/-! ## Consequences of the power bound -/

/-- `4 * M^4 ≤ n` from the power bound, where `M = 2^⌊(c-1)/2⌋`. -/
theorem M_bound_from_size {n : Int} {c : Nat} (hc : 0 < c) (h : hasSizeCondition n c) :
    4 * ((2 : Int) ^ ((c - 1) / 2)) ^ 4 ≤ n := by
  obtain ⟨nn, rfl⟩ := Int.eq_ofNat_of_zero_le h.nonneg
  obtain ⟨h_lo_nat, _⟩ := hasSizeCondition_natCast_iff.mp h
  exact_mod_cast M_bound_from_size_nat hc h_lo_nat

/-- From the power bound, the step's scaler `M = 2^⌊(c-1)/2⌋` is suitable for `n` (needs `0 < c`). -/
theorem isSuitableScaler_of_hasSizeCondition {n M : Int} {c : Nat}
    (hM : M = 2 ^ ((c - 1) / 2)) (hc : 0 < c) (h : hasSizeCondition n c) :
    isSuitableScaler n M := by
  subst hM
  exact ⟨Int.pow_pos (by omega), M_bound_from_size hc h⟩

/-- Base case: at `c = 0` the power bound `1 ≤ n < 4` makes `1` a near square root of `n`. -/
theorem isNearSquareRoot_one_of_hasSizeCondition {n : Int} (h : hasSizeCondition n 0) :
    isNearSquareRoot n 1 := by
  obtain ⟨h_lo, h_hi⟩ := h
  simp only [Nat.zero_add, Int.pow_zero, Int.pow_one] at h_lo h_hi
  exact ⟨by show (1 - 1) * (1 - 1) < n; omega, by show n < (1 + 1) * (1 + 1); omega⟩

end
