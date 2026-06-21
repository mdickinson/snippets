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

/-- The recursion bottoms out at counter `s = 0`, returning `1` regardless of `c` and `n`. -/
private theorem nsqrtRecursive_zero (n c : ℤ) : nsqrtRecursive n c 0 = .ok 1 := by
  unfold nsqrtRecursive; rfl

/-- One unfolding of the recursion at counter `s + 1`, in the key lemma's `M`-form: for the
step's scaler `M = 2^⌊(c-1)/2⌋` (`0 < c`), a successful subcall on the reduced problem
`⌊n / 4M²⌋` returning `0 < a` makes every Python operation take its `.ok` branch, and the step
returns the combined value `Ma + ⌊n / 4Ma⌋`. The Python shift/floor-divide encoding (`2^(2k+2)`,
`2^(k+2)`) and the `key_isqrt_body_eq` body rewrite are discharged here, so the caller works
only with `M`, `4M²`, `4Ma`. -/
private theorem nsqrtRecursive_succ {n c a M : ℤ} {s : ℕ}
    (hM : M = 2 ^ (Int.fdiv (c - 1) 2).toNat) (hc : 0 < c) (ha : 0 < a)
    (h_sub : nsqrtRecursive (Int.fdiv n (4 * M ^ 2)) (Int.fdiv c 2) s = .ok a) :
    nsqrtRecursive n c (s + 1) = .ok (M * a + Int.fdiv n (4 * M * a)) := by
  subst hM
  set k : ℤ := Int.fdiv (c - 1) 2 with hk_def
  have k_nn : 0 ≤ k := Int.fdiv_nonneg (by linarith) (by norm_num)
  have h2k2_nn : (0 : ℤ) ≤ 2 * k + 2 := by linarith
  have hk2_nn : (0 : ℤ) ≤ k + 2 := by linarith
  -- The Python shift `2^(2k+2)` is the key lemma's `4M²`, so the subcall is on `⌊n / 2^(2k+2)⌋`.
  have h_denom : (4 : ℤ) * (2 ^ k.toNat) ^ 2 = 2 ^ (2 * k + 2).toNat := by
    rw [show (2 * k + 2).toNat = 2 * k.toNat + 2 from by omega]; ring
  rw [h_denom] at h_sub
  -- Thread the `.ok` branches to the shift-form body, then rewrite it to `Ma + ⌊n / 4Ma⌋`.
  have hred : nsqrtRecursive n c (s + 1)
      = .ok (a * 2 ^ k.toNat + Int.fdiv (Int.fdiv n (2 ^ (k + 2).toNat)) a) := by
    unfold nsqrtRecursive
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
      pyFloordiv_eq_ok (show (2 : ℤ) ≠ 0 by norm_num), ← hk_def, Except.ok_bind,
      pyRshift_eq_ok h2k2_nn, h_sub,
      pyLshift_eq_ok k_nn, pyRshift_eq_ok hk2_nn, pyFloordiv_eq_ok (ne_of_gt ha)]
    rfl
  rw [hred, key_isqrt_body_eq k_nn ha (rfl : (2 : ℤ) ^ k.toNat = 2 ^ k.toNat)]

/-- Counter descent for the recursive step: a counter seeded tightly at `s + 1` forces `0 < c`,
and the halved counter `⌊c/2⌋` is then tight for `s` (`(c // 2).bit_length() = c.bit_length() - 1`,
`toNat_bitLength_fdiv_two`). Supplies the two facts the step hands to the recursive call. -/
private theorem counter_step {c : ℤ} {s : ℕ} (hc : 0 ≤ c) (hbl : c.bitLength.toNat = s + 1) :
    0 < c ∧ (Int.fdiv c 2).bitLength.toNat = s := by
  have hc_pos : 0 < c := by
    rcases eq_or_lt_of_le hc with h | h
    · rw [← h, show (0 : ℤ).bitLength = 0 from Int.bitLength_eq_zero_iff.mpr rfl] at hbl
      simp at hbl
    · exact h
  exact ⟨hc_pos, by have h := toNat_bitLength_fdiv_two hc_pos; omega⟩

/-- The recursive auxiliary returns a near square root of `n` and **never raises**, given the
size condition and the counter seeded tightly at `s = c.bit_length()`.

Structural induction on `s`. Each case supplies the goal's two facts — the value the function
returns, and that it is a near square root of `n`: the base via `nsqrtRecursive_zero` and
`isNearSquareRoot_one_of_hasSizeCondition`, the step via `nsqrtRecursive_succ` and
`key_isqrt_lemma` (applied to the scaler `M = 2^⌊(c-1)/2⌋`). -/
private theorem nsqrtRecursive_correctness :
    ∀ (s : ℕ) {c n : ℤ},
      c.bitLength.toNat = s → hasSizeCondition c n →
      ∃ a, nsqrtRecursive n c s = .ok a ∧ isNearSquareRoot n a := by
  intro s
  induction s with
  | zero =>
    intro c n hbl hsc
    -- `c.bitLength.toNat = 0` with `0 ≤ c.bitLength` forces `c = 0`.
    have hc0 : c = 0 := Int.bitLength_eq_zero_iff.mp (by have := Int.bitLength_nonneg c; omega)
    subst hc0
    exact ⟨1, nsqrtRecursive_zero n 0, isNearSquareRoot_one_of_hasSizeCondition hsc⟩
  | succ s ih =>
    intro c n hbl hsc
    -- (mechanics) descend the counter: `0 < c`, and `⌊c/2⌋` is tight for the subcall.
    obtain ⟨hc_pos, hbl_step⟩ := counter_step hsc.c_nonneg hbl
    -- `k = ⌊(c-1)/2⌋`; the scaler `M = 2^k` is suitable for `n`.
    set k : ℤ := Int.fdiv (c - 1) 2
    set M : ℤ := 2 ^ k.toNat with hM_def
    have hM : isSuitableScaler n M := isSuitableScaler_of_hasSizeCondition hM_def hc_pos hsc
    -- The recursion solves the reduced problem `⌊n / 4M²⌋`, returning a near √ `a`; the step
    -- returns `Ma + ⌊n / 4Ma⌋`, which the key lemma certifies as a near √ of `n`.
    obtain ⟨a, ha_eq, a_near⟩ := ih hbl_step (size_condition_step hM_def hc_pos hsc)
    exact ⟨M * a + Int.fdiv n (4 * M * a),
           nsqrtRecursive_succ hM_def hc_pos a_near.pos ha_eq,
           key_isqrt_lemma hM a_near⟩

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
      obtain ⟨a, ha_eq, a_near⟩ :=
        nsqrtRecursive_correctness c.bitLength.toNat
          (c := c) (n := n) rfl (size_condition_initial hpos)
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
