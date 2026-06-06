/-
Size-condition lemmas for the isqrt correctness proof.

The "size condition" for `(c, n)` is `4^c ≤ n < 4^(c+1)`. These lemmas
establish:
- the initial size condition holds for `c = (natBitLength n - 1) / 2`,
- the size condition is preserved by the recursive step
  `c ↦ c/2`, `n ↦ n / 2^(2k+2)` where `k = (c-1)/2`,
- `4·M⁴ ≤ n` follows from `4^c ≤ n` for `M = 2^((c-1)/2)`.

The core lemmas are proved at ℕ level using the `natBitLength`
infrastructure. ℤ-level corollaries are provided at the end, packaged as
`hasSizeCondition`, for direct use in Phase 6.
-/

import Isqrt.BitLengthLemmas
import Isqrt.FDivLemmas

/-! ## Helper arithmetic identity -/

/-- For `0 < c`, the "small half" `(c-1)/2`, the "big half" `c/2`, and
the central bit sum to `c`. -/
theorem big_half_little_half {c : ℕ} (hc : 0 < c) :
    (c - 1) / 2 + c / 2 + 1 = c := by
  omega

/-! ## ℕ-level size conditions -/

/-- Initial size condition: for `0 < n`, the choice
`c = (natBitLength n - 1) / 2` satisfies `4^c ≤ n < 4^(c+1)`. -/
theorem size_condition_initial_nat {n : ℕ} (hn : 0 < n) :
    4 ^ ((natBitLength n - 1) / 2) ≤ n ∧
    n < 4 ^ ((natBitLength n - 1) / 2 + 1) := by
  set b := natBitLength n with hb_def
  set c := (b - 1) / 2 with hc_def
  have hb_pos : 0 < b := natBitLength_pos_iff.mpr hn
  refine ⟨?_, ?_⟩
  · -- 4^c ≤ n: 4^c = 2^(2c) ≤ 2^(b-1) ≤ n
    calc 4 ^ c
        = 2 ^ (2 * c) := by rw [show (4 : ℕ) = 2^2 from rfl, ← pow_mul]
      _ ≤ 2 ^ (b - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ n := two_pow_pred_natBitLength_le hn
  · -- n < 4^(c+1): n < 2^b ≤ 2^(2*(c+1)) = 4^(c+1)
    calc n
        < 2 ^ b := lt_two_pow_natBitLength n
      _ ≤ 2 ^ (2 * (c + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 4 ^ (c + 1) := by rw [show (4 : ℕ) = 2^2 from rfl, ← pow_mul]

/-- Size condition preserved by recursive step. Given `4^c ≤ n < 4^(c+1)`
with `0 < c`, the recursive arguments `c' = c/2` and `m = n / 2^(2k+2)`
(where `k = (c-1)/2`) satisfy `4^c' ≤ m < 4^(c'+1)`. -/
theorem size_condition_step_nat {c n : ℕ} (hc : 0 < c)
    (h_lo : 4 ^ c ≤ n) (h_hi : n < 4 ^ (c + 1)) :
    4 ^ (c / 2) ≤ n / 2 ^ (2 * ((c - 1) / 2) + 2) ∧
    n / 2 ^ (2 * ((c - 1) / 2) + 2) < 4 ^ (c / 2 + 1) := by
  set k := (c - 1) / 2 with hk_def
  set c' := c / 2 with hc'_def
  have hsum : k + c' + 1 = c := big_half_little_half hc
  refine ⟨?_, ?_⟩
  · -- 4^c' ≤ n / 2^(2k+2)
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
    calc 4 ^ c' * 2 ^ (2 * k + 2)
        = 2 ^ (2 * c' + (2 * k + 2)) := by
          rw [show (4 : ℕ) = 2^2 from rfl, ← pow_mul, ← pow_add]
      _ = 2 ^ (2 * c) := by congr 1; omega
      _ = 4 ^ c := by rw [show (4 : ℕ) = 2^2 from rfl, ← pow_mul]
      _ ≤ n := h_lo
  · -- n / 2^(2k+2) < 4^(c'+1)
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc n
        < 4 ^ (c + 1) := h_hi
      _ = 2 ^ (2 * (c + 1)) := by
          rw [show (4 : ℕ) = 2^2 from rfl, ← pow_mul]
      _ = 2 ^ (2 * (c' + 1) + (2 * k + 2)) := by congr 1; omega
      _ = 4 ^ (c' + 1) * 2 ^ (2 * k + 2) := by
          rw [show (4 : ℕ) = 2^2 from rfl, ← pow_mul, ← pow_add]

/-- `4·M⁴ ≤ n` from the size condition's lower bound, where `M = 2^((c-1)/2)`. -/
theorem M_bound_from_size_nat {c n : ℕ} (hc : 0 < c) (h_lo : 4 ^ c ≤ n) :
    4 * (2 ^ ((c - 1) / 2)) ^ 4 ≤ n := by
  set k := (c - 1) / 2 with hk_def
  calc 4 * (2 ^ k) ^ 4
      = 2 ^ (4 * k + 2) := by
        rw [show (4 : ℕ) = 2^2 from rfl, ← pow_mul, ← pow_add]
        congr 1; ring
    _ ≤ 2 ^ (2 * c) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 4 ^ c := by rw [show (4 : ℕ) = 2^2 from rfl, ← pow_mul]
    _ ≤ n := h_lo

/-- Size condition at any depth `d ≤ c`: given `4^c ≤ n < 4^(c+1)`, the
depth-`d` value `n / 4^(c-d)` satisfies `4^d ≤ · < 4^(d+1)`. Unlike
`size_condition_step_nat`, this is proved directly from the top condition
(it cannot be iterated bottom-up, since floor division loses information). -/
theorem size_condition_at_depth_nat {c n d : ℕ} (hd : d ≤ c)
    (h_lo : 4 ^ c ≤ n) (h_hi : n < 4 ^ (c + 1)) :
    4 ^ d ≤ n / 4 ^ (c - d) ∧ n / 4 ^ (c - d) < 4 ^ (d + 1) := by
  have hpos : 0 < 4 ^ (c - d) := by positivity
  refine ⟨?_, ?_⟩
  · -- 4^d ≤ n / 4^(c-d)  ⟺  4^d · 4^(c-d) ≤ n
    rw [Nat.le_div_iff_mul_le hpos]
    calc 4 ^ d * 4 ^ (c - d)
        = 4 ^ (d + (c - d)) := by rw [← pow_add]
      _ = 4 ^ c := by rw [Nat.add_sub_cancel' hd]
      _ ≤ n := h_lo
  · -- n / 4^(c-d) < 4^(d+1)  ⟺  n < 4^(d+1) · 4^(c-d)
    rw [Nat.div_lt_iff_lt_mul hpos]
    calc n
        < 4 ^ (c + 1) := h_hi
      _ = 4 ^ (d + 1 + (c - d)) := by rw [show d + 1 + (c - d) = c + 1 from by omega]
      _ = 4 ^ (d + 1) * 4 ^ (c - d) := by rw [pow_add]

/-! ## ℤ-level size condition

`hasSizeCondition c n` means `4^c ≤ n < 4^(c+1)`, the invariant maintained
through the `isqrt_aux` recursion. The ℤ-level lemmas are corollaries of
the ℕ-level ones, with the bridging done once here. -/

/-- The size condition: `4^c ≤ n < 4^(c+1)` (using `c.toNat` so that the
exponent is a natural number). Intended for `0 ≤ c`. -/
def hasSizeCondition (c n : ℤ) : Prop :=
  (4 : ℤ) ^ c.toNat ≤ n ∧ n < (4 : ℤ) ^ (c.toNat + 1)

/-- Initial size condition holds for `c = (pyBitLength n - 1) py// 2`. -/
theorem size_condition_initial {n : ℤ} (hn : 0 < n) :
    hasSizeCondition ((pyBitLength n - 1) py// 2) n := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
  have hm_pos : 0 < m := by exact_mod_cast hn
  have h_bl_pos : 1 ≤ natBitLength m := natBitLength_pos_iff.mpr hm_pos
  -- Convert recursion-depth expression to ℕ.
  have h_toNat : ((pyBitLength (↑m : ℤ) - 1) py// 2).toNat
                  = (natBitLength m - 1) / 2 := by
    show (Int.fdiv (pyBitLength (↑m : ℤ) - 1) 2).toNat = _
    rw [show pyBitLength (↑m : ℤ) = ((natBitLength m : ℕ) : ℤ) from rfl,
        show ((natBitLength m : ℕ) : ℤ) - 1 = ((natBitLength m - 1 : ℕ) : ℤ) from by
          omega,
        show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl,
        Int.toNat_fdiv_of_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)]
    rfl
  unfold hasSizeCondition
  rw [h_toNat]
  obtain ⟨h_lo, h_hi⟩ := size_condition_initial_nat hm_pos
  refine ⟨?_, ?_⟩
  · exact_mod_cast h_lo
  · exact_mod_cast h_hi

/-- Size condition preserved by the recursive step: `c ↦ c py// 2`,
`n ↦ n py>> (2k+2)` where `k = (c - 1) py// 2`. -/
theorem size_condition_step {c n : ℤ} (hc : 0 < c)
    (h : hasSizeCondition c n) :
    hasSizeCondition (c py// 2)
      (pyRshift n (2 * ((c - 1) py// 2) + 2)
        (by have : 0 ≤ ((c - 1) py// 2) :=
              pyFloordiv_nonneg (by linarith) (by norm_num)
            linarith)) := by
  obtain ⟨h_lo, h_hi⟩ := h
  have hn_nonneg : 0 ≤ n := by
    have h4c_nn : (0 : ℤ) ≤ (4 : ℤ) ^ c.toNat := by positivity
    linarith
  -- Reduce c, n to ℕ casts.
  obtain ⟨nn, rfl⟩ := Int.eq_ofNat_of_zero_le hn_nonneg
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc.le
  have hcn_pos : 0 < cn := by exact_mod_cast hc
  -- `c.toNat = cn` etc.
  have hcN : (↑cn : ℤ).toNat = cn := Int.toNat_natCast cn
  -- ((cn : ℤ) py// 2).toNat = cn / 2
  have h_c2 : ((↑cn : ℤ) py// 2).toNat = cn / 2 := by
    show (Int.fdiv (↑cn : ℤ) 2).toNat = _
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl,
        Int.toNat_fdiv_of_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)]
    simp
  -- ((cn - 1 : ℤ) py// 2).toNat = (cn - 1) / 2
  have h_c12 : ((↑cn - 1 : ℤ) py// 2).toNat = (cn - 1) / 2 := by
    show (Int.fdiv (↑cn - 1 : ℤ) 2).toNat = _
    rw [show ((↑cn : ℤ) - 1) = ((cn - 1 : ℕ) : ℤ) from by omega,
        show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl,
        Int.toNat_fdiv_of_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)]
    simp
  -- The shifted value equals the ℤ-cast of the ℕ-level shifted value.
  have h_shift :
      pyRshift (↑nn : ℤ) (2 * ((↑cn - 1 : ℤ) py// 2) + 2) (by
        have : 0 ≤ ((↑cn - 1 : ℤ) py// 2) :=
          pyFloordiv_nonneg (by have : (1:ℤ) ≤ cn := by exact_mod_cast hcn_pos
                                linarith) (by norm_num)
        linarith)
        = ((nn / 2 ^ (2 * ((cn - 1) / 2) + 2) : ℕ) : ℤ) := by
    show Int.fdiv (↑nn : ℤ) (2 ^ (2 * ((↑cn - 1 : ℤ) py// 2) + 2).toNat) = _
    have h_shamt : (2 * ((↑cn - 1 : ℤ) py// 2) + 2).toNat
                  = 2 * ((cn - 1) / 2) + 2 := by
      have h_k_nn : 0 ≤ ((↑cn - 1 : ℤ) py// 2) :=
        pyFloordiv_nonneg (by have : (1:ℤ) ≤ cn := by exact_mod_cast hcn_pos
                              linarith)
                          (by norm_num)
      rw [← h_c12]; omega
    rw [h_shamt,
        show ((2 : ℤ) ^ (2 * ((cn - 1) / 2) + 2))
              = ((2 ^ (2 * ((cn - 1) / 2) + 2) : ℕ) : ℤ) by push_cast; rfl,
        Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg _)]
    rfl
  -- Apply ℕ-level lemma.
  have h_lo_nat : 4 ^ cn ≤ nn := by
    have := h_lo; rw [hcN] at this; exact_mod_cast this
  have h_hi_nat : nn < 4 ^ (cn + 1) := by
    have := h_hi; rw [hcN] at this; exact_mod_cast this
  obtain ⟨step_lo, step_hi⟩ := size_condition_step_nat hcn_pos h_lo_nat h_hi_nat
  -- Assemble the ℤ-level conclusion.
  unfold hasSizeCondition
  rw [h_c2, h_shift]
  refine ⟨?_, ?_⟩
  · exact_mod_cast step_lo
  · exact_mod_cast step_hi

/-- `4 * M^4 ≤ n` from the size condition, where `M = 2^((c-1) py// 2).toNat`. -/
theorem M_bound_from_size {c n : ℤ} (hc : 0 < c) (h : hasSizeCondition c n) :
    4 * ((2 : ℤ) ^ (((c - 1) py// 2).toNat)) ^ 4 ≤ n := by
  obtain ⟨h_lo, _⟩ := h
  have hn_nonneg : 0 ≤ n := by
    have : (0 : ℤ) ≤ (4 : ℤ) ^ c.toNat := by positivity
    linarith
  obtain ⟨nn, rfl⟩ := Int.eq_ofNat_of_zero_le hn_nonneg
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc.le
  have hcn_pos : 0 < cn := by exact_mod_cast hc
  have hcN : (↑cn : ℤ).toNat = cn := Int.toNat_natCast cn
  have h_c12 : ((↑cn - 1 : ℤ) py// 2).toNat = (cn - 1) / 2 := by
    show (Int.fdiv (↑cn - 1 : ℤ) 2).toNat = _
    rw [show ((↑cn : ℤ) - 1) = ((cn - 1 : ℕ) : ℤ) from by omega,
        show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl,
        Int.toNat_fdiv_of_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)]
    simp
  rw [h_c12]
  have h_lo_nat : 4 ^ cn ≤ nn := by
    have := h_lo; rw [hcN] at this; exact_mod_cast this
  have h_nat := M_bound_from_size_nat hcn_pos h_lo_nat
  exact_mod_cast h_nat

/-- Size condition at any depth `0 ≤ d ≤ c`: derived directly from
`hasSizeCondition c n`, the value `n` takes at depth `d`,
`⌊n / 4^(c-d)⌋ = n >> 2(c-d)`, again satisfies the size condition (now for `d`).
This is the `(c,n)`-only fact the iterative isqrt's loop property leans on at
both its seed and its preservation step. -/
theorem size_condition_at_depth {c n d : ℤ} (hd_lo : 0 ≤ d) (hd_hi : d ≤ c)
    (h : hasSizeCondition c n) :
    hasSizeCondition d (Int.fdiv n (4 ^ (c - d).toNat)) := by
  obtain ⟨h_lo, h_hi⟩ := h
  have hn_nonneg : 0 ≤ n := by
    have : (0 : ℤ) ≤ (4 : ℤ) ^ c.toNat := by positivity
    linarith
  obtain ⟨nn, rfl⟩ := Int.eq_ofNat_of_zero_le hn_nonneg
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans hd_lo hd_hi)
  obtain ⟨dn, rfl⟩ := Int.eq_ofNat_of_zero_le hd_lo
  have hcN : (↑cn : ℤ).toNat = cn := Int.toNat_natCast cn
  have hdN : (↑dn : ℤ).toNat = dn := Int.toNat_natCast dn
  have hdc : dn ≤ cn := by exact_mod_cast hd_hi
  -- (c - d).toNat = cn - dn
  have h_cd : ((↑cn - ↑dn : ℤ)).toNat = cn - dn := by
    rw [show ((↑cn : ℤ) - ↑dn) = ((cn - dn : ℕ) : ℤ) from (Nat.cast_sub hdc).symm]
    exact Int.toNat_natCast _
  -- The fdiv of nonneg-nat casts is the natCast of the ℕ division.
  have h_bridge : Int.fdiv (↑nn : ℤ) ((4 : ℤ) ^ (cn - dn))
                    = ((nn / 4 ^ (cn - dn) : ℕ) : ℤ) := by
    rw [show ((4 : ℤ) ^ (cn - dn)) = ((4 ^ (cn - dn) : ℕ) : ℤ) from by push_cast; rfl,
        Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg _)]
    rfl
  -- Apply the ℕ-level lemma.
  have h_lo_nat : 4 ^ cn ≤ nn := by
    have := h_lo; rw [hcN] at this; exact_mod_cast this
  have h_hi_nat : nn < 4 ^ (cn + 1) := by
    have := h_hi; rw [hcN] at this; exact_mod_cast this
  obtain ⟨step_lo, step_hi⟩ := size_condition_at_depth_nat hdc h_lo_nat h_hi_nat
  -- Assemble the ℤ-level conclusion.
  unfold hasSizeCondition
  rw [hdN, h_cd, h_bridge]
  refine ⟨?_, ?_⟩
  · exact_mod_cast step_lo
  · exact_mod_cast step_hi
