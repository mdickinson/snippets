/-
Correctness of the iterative integer square root `isqrtIterative`.

Strategy: reuse the recursive proof's algebra. The loop's persistent `d` climbs
the chain `c >> j` that the recursion descends, so one iteration is exactly one
`key_isqrt_lemma` step at parent depth `d`. We prove the loop property

    P st := isNearSqrt st.a (⌊n / 4^(c - st.d)⌋)

(near-√ only — the size condition is pulled fresh from `size_condition_at_depth`
at seed and step) holds at the loop result via `pyWhile_invariant`, then read off
`isNearSqrt a n` at the exit (`s = 0 ⟹ d = c ⟹ N_c = n`) and finish with the
return line `a if a*a ≤ n else a-1`, exactly as `isqrt_is_sqrt` does.

The main result is `isqrtIterative_is_sqrt`, the same statement as
`isqrt_is_sqrt`. See `PLAN.md` (Iterative variant) and `CONTEXT.md`.
-/

import Isqrt.Iterative
import Isqrt.KeyLemma
import Isqrt.SizeConditions

/-! ## Near-square-root of the loop result -/

/-- The loop result is a near square root of `n`. Proved by `pyWhile_invariant`
with the loop property `P st := isNearSqrt st.a ⌊n/4^(c-st.d)⌋`: the seed
(`d = 0`) is `isNearSqrt 1 ⌊n/4^c⌋` (base case), each step is one
`key_isqrt_lemma`, and at the exit `s = 0` forces `d = c`, collapsing the
divisor to `4^0 = 1`. -/
theorem isqrtIterativeLoop_near {c n : ℤ} (hc : 0 ≤ c) (hn : 0 < n)
    (hsc : hasSizeCondition c n) :
    isNearSqrt (isqrtIterativeLoop c n hc hn.le).val.val.a n := by
  set result := isqrtIterativeLoop c n hc hn.le with hres
  -- The loop property holds at the result.
  have hP : isNearSqrt result.val.val.a
              (Int.fdiv n (4 ^ (c - result.val.val.d).toNat)) := by
    rw [hres]
    unfold isqrtIterativeLoop
    refine pyWhile_invariant
      (P := fun st : IterSigma c =>
        isNearSqrt st.val.a (Int.fdiv n (4 ^ (c - st.val.d).toNat)))
      _ ?hinit ?hstep
    case hinit =>
      -- Seed: d = 0, a = 1, so isNearSqrt 1 ⌊n/4^(c-0)⌋.
      show isNearSqrt (1 : ℤ) (Int.fdiv n (4 ^ (c - 0).toNat))
      obtain ⟨hlo, hhi⟩ := size_condition_at_depth (d := 0) le_rfl hc hsc
      simp only [Int.toNat_zero, pow_zero, zero_add, pow_one] at hlo hhi
      refine ⟨?_, ?_⟩
      · show (1 - 1) * (1 - 1) < Int.fdiv n (4 ^ (c - 0).toNat); nlinarith [hlo]
      · show Int.fdiv n (4 ^ (c - 0).toNat) < (1 + 1) * (1 + 1); nlinarith [hhi]
    case hstep =>
      -- One iteration = one `key_isqrt_lemma` step at parent depth `d_new`.
      intro st h hPst
      obtain ⟨hs_lb, hs_lt, hd_old_eq, ha_old_pos⟩ := st.property
      simp only [iterBody_a, iterBody_d, pyLshift_def, pyRshift_def, pyFloordiv_def]
      set s := st.val.s
      set d_old := st.val.d
      set a_old := st.val.a
      set d_new := Int.fdiv c (2 ^ s.toNat) with hd_new_def
      set N_new := Int.fdiv n (4 ^ (c - d_new).toNat) with hN_new_def
      -- Positivity / ordering of the depths. (d_old ≤ c is not needed: it
      -- follows from `hK` and `hd_new_le` wherever `omega` wants it.)
      have hd_old_nonneg : 0 ≤ d_old := by
        rw [hd_old_eq]; exact pyRshift_nonneg hc
      have hd_new_nonneg : 0 ≤ d_new := by
        rw [hd_new_def]; exact Int.fdiv_nonneg hc (by positivity)
      have hd_new_le : d_new ≤ c := by
        rw [hd_new_def]; exact Int.fdiv_le_self_of_nonneg hc (by positivity)
      -- Left-shift amount nonneg, hence d_new ≥ 1.
      have hK : 0 ≤ d_new - d_old - 1 := by
        rw [hd_new_def]; exact iter_lshift_nonneg hc h hs_lt hd_old_eq
      have hd_new_pos : 0 < d_new := by omega
      -- d_old = d_new / 2 (the halving link).
      have h_halve : d_old = Int.fdiv d_new 2 := by
        rw [hd_old_eq, hd_new_def]; exact pyRshift_succ c s h
      -- k and M = 2^k.
      set k := (d_new - 1) py// 2 with hk_def
      have hk_eq : k = d_new - d_old - 1 := by
        rw [hk_def]; simp only [pyFloordiv_def]; rw [h_halve,
            Int.fdiv_eq_ediv_of_nonneg (d_new - 1) (by norm_num : (0 : ℤ) ≤ 2),
            Int.fdiv_eq_ediv_of_nonneg d_new (by norm_num : (0 : ℤ) ≤ 2)]
        omega
      set M := (2 : ℤ) ^ k.toNat with hM_def
      have hM_pos : 0 < M := by rw [hM_def]; positivity
      -- 4·M⁴ ≤ N_new, from the size condition at depth d_new.
      have hsc_new : hasSizeCondition d_new N_new := by
        rw [hN_new_def]; exact size_condition_at_depth hd_new_nonneg hd_new_le hsc
      have hM4 : 4 * M ^ 4 ≤ N_new := by
        have := M_bound_from_size hd_new_pos hsc_new
        rwa [← hk_def, ← hM_def] at this
      -- Near-√ at the child: isNearSqrt a_old ⌊N_new/4M²⌋ = isNearSqrt a_old N_old.
      have h_div_bridge :
          Int.fdiv N_new (4 * M ^ 2) = Int.fdiv n (4 ^ (c - d_old).toNat) := by
        rw [hN_new_def, Int.fdiv_fdiv_eq_fdiv_mul n (by positivity) (by positivity)]
        congr 1
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num, hM_def]
        simp only [← pow_mul, ← pow_add]
        congr 1
        omega
      have h_near : isNearSqrt a_old (Int.fdiv N_new (4 * M ^ 2)) := by
        rw [h_div_bridge]; exact hPst
      -- The body's new `a` is exactly the `key_isqrt_lemma` output.
      have hMa_nn : (0 : ℤ) ≤ 4 * M * a_old :=
        mul_nonneg (mul_nonneg (by norm_num) hM_pos.le) ha_old_pos.le
      have hX :
          a_old * 2 ^ (d_new - d_old - 1).toNat
              + Int.fdiv (Int.fdiv n (2 ^ (2 * c - d_new - d_old + 1).toNat)) a_old
            = M * a_old + Int.fdiv N_new (4 * M * a_old) := by
        congr 1
        · rw [hM_def, show (d_new - d_old - 1).toNat = k.toNat from by rw [hk_eq]]
          ring
        · rw [hN_new_def,
              Int.fdiv_fdiv_eq_fdiv_mul n (by positivity) ha_old_pos.le,
              Int.fdiv_fdiv_eq_fdiv_mul n (by positivity) hMa_nn]
          congr 1
          have hpow_a : (2 : ℤ) ^ (2 * c - d_new - d_old + 1).toNat
                          = 4 ^ (c - d_new).toNat * (4 * M) := by
            rw [hM_def, show (4 : ℤ) = 2 ^ 2 by norm_num]
            simp only [← pow_mul, ← pow_add]
            congr 1
            omega
          rw [hpow_a]; ring
      rw [hX]
      exact key_isqrt_lemma hM_pos ha_old_pos hM4 h_near
  -- Exit: ¬ (0 ≤ s) forces s < 0, so (s+1).toNat = 0 and d = c >> 0 = c.
  have hd : result.val.val.d = c := by
    have hs_neg : result.val.val.s < 0 := by have := result.property; omega
    have hdc := result.val.property.hd_eq
    simp only [pyRshift_def] at hdc
    rw [show (result.val.val.s + 1).toNat = 0 by omega] at hdc
    simpa using hdc
  rw [hd] at hP
  simpa using hP

/-! ## Correctness of `isqrtIterative` -/

/-- Main correctness theorem for the iterative form: `isqrtIterative n` is the
floor of `√n`. Same statement as `isqrt_is_sqrt`. -/
theorem isqrtIterative_is_sqrt (n : ℤ) (hn : 0 ≤ n) :
    isIntegerSqrt (isqrtIterative n hn) n := by
  show isqrtIterative n hn * isqrtIterative n hn ≤ n ∧
        n < (isqrtIterative n hn + 1) * (isqrtIterative n hn + 1)
  by_cases hn0 : n = 0
  · subst hn0; simp [isqrtIterative]
  · have hn_pos : 0 < n := lt_of_le_of_ne hn (Ne.symm hn0)
    have hc : 0 ≤ (pyBitLength n - 1) py// 2 := isqrt_c_nonneg hn0
    have h_near :
        isNearSqrt (isqrtIterativeLoop ((pyBitLength n - 1) py// 2) n hc hn_pos.le).val.val.a n :=
      isqrtIterativeLoop_near hc hn_pos (size_condition_initial hn_pos)
    unfold isqrtIterative
    simp only [hn0, ↓reduceDIte]
    set a := (isqrtIterativeLoop ((pyBitLength n - 1) py// 2) n hc hn_pos.le).val.val.a
    obtain ⟨h_lo, h_hi⟩ := h_near
    by_cases h_gt : a * a > n
    · rw [if_pos h_gt]
      have h_lt : n < a * a := h_gt
      exact ⟨by nlinarith [h_lo], by nlinarith [h_lt]⟩
    · rw [if_neg h_gt]
      have h_le : a * a ≤ n := not_lt.mp h_gt
      exact ⟨h_le, by nlinarith [h_hi]⟩
