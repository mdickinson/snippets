/-
Correctness of `isqrt n`: it returns the floor of `√n`.

Strategy: strong induction on `c.toNat` for `isqrt_aux`, where the
size-condition invariant `4^c ≤ n < 4^(c+1)` (from `Isqrt.SizeConditions`)
is preserved by each recursive step. The inductive step combines
`isqrt_aux_step_val` (unfolds the recursion) with `key_isqrt_lemma`
(the algebraic correctness statement from `Isqrt.KeyLemma`). The main
result is `isqrt_is_sqrt`.
-/

import Isqrt.Algorithm
import Isqrt.FDivLemmas
import Isqrt.KeyLemma
import Isqrt.SizeConditions

/-! ## Correctness of `isqrt_aux` -/

/-- Helper: `(j + 2).toNat = j.toNat + 2` for `0 ≤ j`. -/
private theorem toNat_add_two {j : ℤ} (hj : 0 ≤ j) :
    (j + 2).toNat = j.toNat + 2 := by
  obtain ⟨j0, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  rw [Int.toNat_natCast]; omega

/-- Helper: `(2 * j + 2).toNat = 2 * j.toNat + 2` for `0 ≤ j`. -/
private theorem toNat_two_mul_add_two {j : ℤ} (hj : 0 ≤ j) :
    (2 * j + 2).toNat = 2 * j.toNat + 2 := by
  obtain ⟨j0, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  rw [Int.toNat_natCast]; omega

/-- Unfolding lemma for the recursive case of `isqrt_aux`. Exposes the
algorithm's return value in terms of the recursive subproblem's value `a`. -/
private theorem isqrt_aux_step_val {c n : ℤ} (hc : 0 ≤ c) (hn : 0 ≤ n)
    (hc_pos : 0 < c) :
    let k := (c - 1) py// 2
    let kn : 0 ≤ k := pyFloordiv_nonneg (by linarith) (by norm_num)
    let d := c py// 2
    let dn : 0 ≤ d := pyFloordiv_nonneg hc (by norm_num)
    let m := pyRshift n (2 * k + 2) (by linarith)
    let mn : 0 ≤ m := pyRshift_nonneg hn
    let a := (isqrt_aux d m dn mn).val
    (isqrt_aux c n hc hn).val =
      a * 2 ^ k.toNat + (Int.fdiv n (2 ^ (k + 2).toNat)).fdiv a := by
  intro k kn d dn m mn a
  unfold isqrt_aux
  simp [hc_pos.ne']
  rfl

/-- The aux function is a near square root for any size-conformant `(c, n)`.

For `0 < n` satisfying the size condition `4^c ≤ n < 4^(c+1)`, the value
returned by `isqrt_aux c n` is a near square root of `n`:
`(a - 1)² < n ∧ n < (a + 1)²`. -/
private theorem isqrt_aux_correctness :
    ∀ (cn : ℕ) {c n : ℤ} (hc : 0 ≤ c) (hn : 0 < n),
      c.toNat = cn → hasSizeCondition c n →
      isNearSqrt (isqrt_aux c n hc hn.le).val n := by
  intro cn
  induction cn using Nat.strong_induction_on with
  | _ cn ih =>
    intro c n hc hn hcn ⟨h_lo, h_hi⟩
    by_cases hc0 : c = 0
    · -- Base case: c = 0, size condition gives 1 ≤ n < 4
      subst hc0
      have h_val : (isqrt_aux 0 n hc hn.le).val = 1 := by
        unfold isqrt_aux; rfl
      simp only [Int.toNat_zero, pow_zero, zero_add, pow_one] at h_lo h_hi
      refine ⟨?_, ?_⟩
      · show ((isqrt_aux 0 n hc hn.le).val - 1) ^ 2 < n
        rw [h_val]; ring_nf; linarith
      · show n < ((isqrt_aux 0 n hc hn.le).val + 1) ^ 2
        rw [h_val]; ring_nf; linarith
    · -- Inductive case: c > 0
      have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      set k := (c - 1) py// 2 with hk_def
      have k_nn : 0 ≤ k := pyFloordiv_nonneg (by linarith) (by norm_num)
      set d := c py// 2 with hd_def
      have d_nn : 0 ≤ d := pyFloordiv_nonneg hc (by norm_num)
      have h2k2_nn : (0 : ℤ) ≤ 2 * k + 2 := by linarith
      set m := pyRshift n (2 * k + 2) h2k2_nn with hm_def
      have m_nn : 0 ≤ m := pyRshift_nonneg hn.le
      -- Size condition is preserved by the recursive step.
      have hsc_step : hasSizeCondition d m :=
        size_condition_step hc_pos ⟨h_lo, h_hi⟩
      have m_pos : 0 < m := by
        have h4d_nn : (0 : ℤ) < (4 : ℤ) ^ d.toNat := by positivity
        linarith [hsc_step.1]
      -- The recursion decreases on `c.toNat`.
      have hd_toNat_lt : d.toNat < cn := by
        rw [← hcn, hd_def]
        show (Int.fdiv c 2).toNat < c.toNat
        obtain ⟨c0, rfl⟩ := Int.eq_ofNat_of_zero_le hc
        rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl,
            Int.toNat_fdiv_of_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)]
        simp [Int.toNat_natCast]
        have : 0 < c0 := by exact_mod_cast hc_pos
        omega
      -- Apply induction hypothesis to the recursive call.
      have ih_result := ih d.toNat hd_toNat_lt d_nn m_pos rfl hsc_step
      set a := (isqrt_aux d m d_nn m_pos.le).val with ha_def
      have a_pos : 0 < a := (isqrt_aux d m d_nn m_pos.le).property
      set M := (2 : ℤ) ^ k.toNat with hM_def
      have M_pos : 0 < M := by positivity
      -- Bridge: `m = n.fdiv (4 * M²)`.
      have hm_eq : m = n.fdiv (4 * M ^ 2) := by
        show Int.fdiv n (2 ^ (2 * k + 2).toNat) = _
        rw [toNat_two_mul_add_two k_nn, hM_def]
        congr 1; ring
      -- M_bound: `4 * M⁴ ≤ n`.
      have hM4 : 4 * M ^ 4 ≤ n := by
        have := M_bound_from_size hc_pos ⟨h_lo, h_hi⟩
        rwa [← hk_def, ← hM_def] at this
      -- Apply the key algebraic lemma.
      have a_near' : isNearSqrt a (n.fdiv (4 * M ^ 2)) := hm_eq ▸ ih_result
      have h_key := key_isqrt_lemma M_pos a_pos hM4 a_near'
      -- Unfold the algorithm to expose its return value, then rewrite to
      -- the form expected by `h_key`.
      have val_eq : (isqrt_aux c n hc hn.le).val = M * a + n.fdiv (4 * M * a) := by
        have step1 := isqrt_aux_step_val hc hn.le hc_pos
        -- `step1` has the form  isqrt_aux c n = a * 2^k.toNat + ...
        simp only at step1
        rw [step1, toNat_add_two k_nn]
        have h_pow : (2 : ℤ) ^ (k.toNat + 2) = 4 * M := by
          rw [hM_def, pow_add]; ring
        rw [h_pow]
        rw [Int.fdiv_fdiv_eq_fdiv_mul n (by positivity : (0 : ℤ) ≤ 4 * M) a_pos.le]
        ring
      show isNearSqrt (isqrt_aux c n hc hn.le).val n
      rw [val_eq]
      exact h_key

/-! ## Correctness of `isqrt` -/

/-- Main correctness theorem: `isqrt n` is the floor of `√n`. -/
theorem isqrt_is_sqrt (n : ℤ) (hn : 0 ≤ n) :
    isIntegerSqrt (isqrt n hn) n := by
  show isqrt n hn * isqrt n hn ≤ n ∧ n < (isqrt n hn + 1) * (isqrt n hn + 1)
  unfold isqrt
  by_cases hn0 : n = 0
  · subst hn0
    simp
  · simp only [hn0, ↓reduceDIte]
    have hn_pos : 0 < n := lt_of_le_of_ne hn (Ne.symm hn0)
    set c := (pyBitLength n - 1) py// 2 with hc_def
    have hc_nn : 0 ≤ c := isqrt_c_nonneg hn0
    set a := (isqrt_aux c n hc_nn hn_pos.le).val with ha_def
    -- Apply isqrt_aux_correctness with the initial size condition.
    have hsc := size_condition_initial hn_pos
    have h_near : isNearSqrt a n :=
      isqrt_aux_correctness c.toNat hc_nn hn_pos rfl hsc
    obtain ⟨h_lo, h_hi⟩ := h_near
    by_cases h_lt : n < a * a
    · simp only [h_lt, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · nlinarith [h_lo]
      · nlinarith [h_lt]
    · simp only [h_lt, ↓reduceIte]
      have h_le : a * a ≤ n := not_lt.mp h_lt
      refine ⟨?_, ?_⟩
      · nlinarith [h_le]
      · nlinarith [h_hi]
