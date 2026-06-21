/-
Correctness of the recursive monadic integer square root `isqrtRecursive`.

Strategy: structural induction on the counter `s` for `nsqrtRecursive`, carrying
the **tight** invariant `c.bitLength.toNat = s` alongside the size condition
`4^c ≤ n < 4^(c+1)` (from `Isqrt.Proofs.SizeConditions`). The invariant must be tight,
not merely an upper bound: an overshoot would reach `c = 0` with `s > 0`, where
`k = (c-1) // 2 = -1` and the body's `a << k` would raise `ValueError`.

Each inductive step discharges the `.ok`-ness of every monadic operation — proving
no `//`, `>>`, or `<<` ever raises when `s = c.bit_length()` and `c ≥ 0` — and then
applies the core algebraic step `key_isqrt_lemma` (`Isqrt.Proofs.KeyLemma`) to the
recursive subproblem's value. The top-level result `isCorrectIsqrt_isqrtRecursive`
establishes the `isCorrectIsqrt` contract, mirroring the iterative `isCorrectIsqrt_isqrtIterative`.
-/

module

meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.Positivity
meta import Mathlib.Tactic.Ring
public import Isqrt.Definitions.IsqrtRecursive
public import Isqrt.Definitions.Specification
import Isqrt.Definitions.PythonPrimitives
import Isqrt.Proofs.SizeConditions
import Isqrt.Proofs.KeyLemma
import Isqrt.Proofs.PythonPrimitivesLemmas

public section

/-- The recursive auxiliary is a positive near square root for any size-conformant
`(c, n)`, **and never raises**, provided the counter is seeded tightly at
`s = c.bit_length()`.

Structural induction on `s`: the base `s = 0` forces `c = 0` (so the function
returns `1`, a near-√ of the `1 ≤ n < 4` that the size condition pins down), and
the step `s + 1` discharges every monadic operation to `.ok` — the recursive call
via the induction hypothesis (whose bit-length premise is `toNat_bitLength_fdiv_two`),
the shifts/divisions via their nonneg side conditions — then closes with the core
`key_isqrt_lemma` algebra of `Isqrt.Proofs.KeyLemma` (the same per-step lemma the iterative
proof `Isqrt.Proofs.IterativeCorrectness` applies). -/
private theorem nsqrtRecursive_correctness :
    ∀ (s : ℕ) {c n : ℤ}, 0 ≤ c → 0 < n →
      c.bitLength.toNat = s → hasSizeCondition c n →
      ∃ a, nsqrtRecursive n c s = .ok a ∧ 0 < a ∧ isNearSquareRoot n a := by
  intro s
  induction s with
  | zero =>
    intro c n hc hn hbl hsc
    -- `c.bitLength.toNat = 0` with `0 ≤ c` forces `c = 0`.
    have hbl_nn := Int.bitLength_nonneg c
    have hc0 : c = 0 := Int.bitLength_eq_zero_iff.mp (by omega)
    subst hc0
    obtain ⟨h_lo, h_hi⟩ := hsc
    simp only [Int.toNat_zero, pow_zero, zero_add, pow_one] at h_lo h_hi
    -- `nsqrtRecursive n 0 0 = .ok 1`, and `1 ≤ n < 4` gives the near-√ property.
    exact ⟨1, by unfold nsqrtRecursive; rfl, one_pos, by show (1 - 1) * (1 - 1) < n; omega,
                            by show n < (1 + 1) * (1 + 1); omega⟩
  | succ s ih =>
    intro c n hc hn hbl hsc
    -- `c.bitLength.toNat = s + 1 > 0` forces `0 < c`.
    have hc_pos : 0 < c := by
      rcases eq_or_lt_of_le hc with h | h
      · rw [← h, show (0 : ℤ).bitLength = 0 from Int.bitLength_eq_zero_iff.mpr rfl] at hbl
        simp at hbl
      · exact h
    -- The recursive arguments, in `Int.fdiv` form (matching the `Except` ops).
    set k : ℤ := Int.fdiv (c - 1) 2 with hk_def
    set d : ℤ := Int.fdiv c 2 with hd_def
    set m : ℤ := Int.fdiv n (2 ^ (2 * k + 2).toNat) with hm_def
    have k_nn : 0 ≤ k := Int.fdiv_nonneg (by linarith) (by norm_num)
    have d_nn : 0 ≤ d := Int.fdiv_nonneg hc (by norm_num)
    have h2k2_nn : (0 : ℤ) ≤ 2 * k + 2 := by linarith
    have hk2_nn : (0 : ℤ) ≤ k + 2 := by linarith
    -- Size condition is preserved by the step.
    have hsc_step : hasSizeCondition d m := size_condition_step hc_pos hsc
    have m_pos : 0 < m := by
      obtain ⟨hlo, _⟩ := hsc_step
      have : (0 : ℤ) < 4 ^ d.toNat := by positivity
      linarith
    -- The tight bit-length invariant descends: `(c // 2).bit_length() = c.bit_length() - 1`.
    have hbl_step : d.bitLength.toNat = s := by
      have h := toNat_bitLength_fdiv_two hc_pos
      rw [← hd_def] at h
      omega
    -- Induction hypothesis on the recursive subproblem.
    obtain ⟨a, ha_eq, a_pos, a_near⟩ := ih d_nn m_pos hbl_step hsc_step
    -- Reduce the `do`-block: every operation takes its `.ok` branch.
    have hred : nsqrtRecursive n c (s + 1)
        = .ok (a * 2 ^ k.toNat + Int.fdiv (Int.fdiv n (2 ^ (k + 2).toNat)) a) := by
      unfold nsqrtRecursive
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
        pyFloordiv_eq_ok (show (2 : ℤ) ≠ 0 by norm_num),
        ← hk_def, ← hd_def, Except.ok_bind,
        pyRshift_eq_ok h2k2_nn, ← hm_def, ha_eq,
        pyLshift_eq_ok k_nn, pyRshift_eq_ok hk2_nn,
        pyFloordiv_eq_ok (ne_of_gt a_pos)]
      rfl
    -- Algebra: the returned value is the `key_isqrt_lemma` output for `M = 2^k.toNat`.
    set M := (2 : ℤ) ^ k.toNat with hM_def
    have M_pos : 0 < M := by positivity
    have hm_eq : m = Int.fdiv n (4 * M ^ 2) := by
      rw [hm_def, show (2 * k + 2).toNat = 2 * k.toNat + 2 from by omega, hM_def]
      congr 1; ring
    have hM4 : 4 * M ^ 4 ≤ n := by
      have h := M_bound_from_size hc_pos hsc
      rwa [← hk_def, ← hM_def] at h
    have a_near' : isNearSquareRoot (Int.fdiv n (4 * M ^ 2)) a := hm_eq ▸ a_near
    have val_eq :
        a * 2 ^ k.toNat + Int.fdiv (Int.fdiv n (2 ^ (k + 2).toNat)) a
          = M * a + Int.fdiv n (4 * M * a) :=
      key_isqrt_body_eq k_nn a_pos hM_def
    refine ⟨_, hred, ?_, ?_⟩
    · -- positivity of the returned value
      exact add_pos_of_pos_of_nonneg (mul_pos a_pos (by positivity))
        (Int.fdiv_nonneg (Int.fdiv_nonneg hn.le (by positivity)) a_pos.le)
    · -- near-√ via the key lemma
      rw [val_eq]; exact key_isqrt_lemma M_pos hM4 a_near'

/-- Correctness of the recursive monadic integer square root `isqrtRecursive`.

For nonnegative `n` it returns a value `a = ⌊√n⌋` (`isIntegerSquareRoot n a`); for
negative `n` it raises exactly the `ValueError` CPython does. The returns proof
reduces the `do`-block to the `nsqrtRecursive` call characterised by `nsqrtRecursive_correctness`
— establishing en route that none of the `Except` operations ever takes its error
branch for `n ≥ 0` — and closes the `n ≥ 1` case with the final `a-1`/`a`
adjustment (`isNearSquareRoot.toIntegerSquareRoot`), which the recursive source's
`a - 1 if n < a * a else a` already matches verbatim. The contract `isCorrectIsqrt`
is the same one the iterative `isCorrectIsqrt_isqrtIterative` establishes. -/
theorem isCorrectIsqrt_isqrtRecursive : isCorrectIsqrt isqrtRecursive := by
  refine ⟨?_, ?_⟩
  · -- Nonnegative `n`: the recursion runs, never raises, and returns `⌊√n⌋`.
    intro n hn
    show ∃ a, returns (isqrtRecursive n) a ∧ isIntegerSquareRoot n a
    rcases eq_or_lt_of_le hn with rfl | hpos
    · -- n = 0: special-cased to 0.
      refine ⟨0, ?_, ?_⟩
      · show isqrtRecursive 0 = .ok 0; unfold isqrtRecursive; norm_num; rfl
      · show isIntegerSquareRoot 0 0; unfold isIntegerSquareRoot; norm_num
    · -- 0 < n: the recursion runs and never raises.
      have hn0 : n ≠ 0 := ne_of_gt hpos
      set c : ℤ := Int.fdiv (n.bitLength - 1) 2 with hc_def
      obtain ⟨a, ha_eq, _a_pos, a_near⟩ :=
        nsqrtRecursive_correctness c.bitLength.toNat
          (c := c) (n := n) (isqrt_c_nonneg hn0) hpos rfl (size_condition_initial hpos)
      have hred : isqrtRecursive n = .ok (if n < a * a then a - 1 else a) := by
        conv_lhs => unfold isqrtRecursive
        simp only [if_neg (show ¬ n < 0 by omega), if_neg hn0, pure_bind,
          pyFloordiv_eq_ok (show (2 : ℤ) ≠ 0 by norm_num), ← hc_def]
        rw [Except.ok_bind, ha_eq]
        rfl
      exact ⟨_, hred, a_near.toIntegerSquareRoot⟩
  · -- Negative `n`: the first guard raises, short-circuiting the `do` block.
    intro n hn
    show raises (isqrtRecursive n) (.valueError "isqrt() argument must be nonnegative")
    have herr : isqrtRecursive n
        = .error (.valueError "isqrt() argument must be nonnegative") := by
      unfold isqrtRecursive; rw [if_pos hn]; rfl
    exact herr

end
