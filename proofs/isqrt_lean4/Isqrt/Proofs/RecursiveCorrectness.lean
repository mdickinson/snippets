/-
Correctness of the recursive monadic integer square root `isqrtRecursive`.

The proof keeps the mechanics out of the mathematics: `nsqrtRecursive_base` and
`nsqrtRecursive_succ` reduce each recursion step to its returned value — discharging the
`.ok`-ness of every Python `//`, `>>`, `<<` and the shift↔`4M²` translation — so that
`nsqrtRecursive_correctness` reads as the mathematical argument alone. The top-level
`isCorrectIsqrt_isqrtRecursive` wraps it in the `isCorrectIsqrt` contract, like the iterative
`isCorrectIsqrt_isqrtIterative`.
-/

module

public import Isqrt.Definitions.IsqrtRecursive
public import Isqrt.Definitions.Specification
import Isqrt.Definitions.PythonPrimitives
import Isqrt.Proofs.SizeConditions
import Isqrt.Proofs.KeyLemma
import Isqrt.Proofs.PythonPrimitivesLemmas

/-- The recursion bottoms out at `c ≤ 0`, returning `1` regardless of `n`. -/
theorem nsqrtRecursive_base (n : Int) {c : Int} (hc : c ≤ 0) :
    nsqrtRecursive n c = .ok 1 := by
  unfold nsqrtRecursive; rw [if_pos hc]; rfl

/-- One unfolding of the recursion at `0 < c`, in the key lemma's `M`-form: for the step's
scaler `M = 2^⌊(c-1)/2⌋` (`0 < c`), a successful subcall on the reduced problem `⌊n / 4M²⌋`
returning `0 < a` makes every Python operation take its `.ok` branch, and the step returns
the combined value `Ma + ⌊n / 4Ma⌋`. The Python shift/floor-divide encoding (`2^(2k+2)`,
`2^(k+2)`) and the `key_isqrt_body_eq` body rewrite are discharged here, so the caller works
only with `M`, `4M²`, `4Ma`. -/
theorem nsqrtRecursive_succ {n c a M : Int}
    (hM : M = 2 ^ ((c - 1).fdiv 2).toNat) (hc : 0 < c) (ha : 0 < a)
    (h_sub : nsqrtRecursive (n.fdiv (4 * M ^ 2)) (c.fdiv 2) = .ok a) :
    nsqrtRecursive n c = .ok (M * a + n.fdiv (4 * M * a)) := by
  subst hM
  let k := (c - 1).fdiv 2
  have hk_def : k = (c - 1).fdiv 2 := rfl
  have k_nn : 0 ≤ k := by grind only
  have h2k2_nn : 0 ≤ 2 * k + 2 := by omega
  have hk2_nn : 0 ≤ k + 2 := by omega
  -- The subcall's `4M²` denominator is the Python shift `2^(2k+2)`.
  rw [four_mul_two_pow_sq k_nn] at h_sub
  -- Thread the `.ok` branches to the shift-form body, then rewrite it to `Ma + ⌊n / 4Ma⌋`.
  have hred : nsqrtRecursive n c
      = .ok (a * 2 ^ k.toNat + (n.fdiv (2 ^ (k + 2).toNat)).fdiv a) := by
    unfold nsqrtRecursive
    simp only [if_neg (Int.not_le.mpr hc),
      pyFloordiv_eq_ok (show 2 ≠ 0 by decide), ← hk_def, Except.ok_bind,
      pyRshift_eq_ok h2k2_nn, h_sub,
      pyLshift_eq_ok k_nn, pyRshift_eq_ok hk2_nn, pyFloordiv_eq_ok (Int.ne_of_gt ha)]
    rfl
  rw [hred, key_isqrt_body_eq k_nn ha (rfl : (2 : Int) ^ k.toNat = 2 ^ k.toNat)]

/-- The recursive auxiliary returns a near square root of `n` and **never raises**, given the
size condition on `(c, n)`.

Each case supplies the goal's two facts — the value the function returns, and that it is a
near square root of `n`. The base case `c ≤ 0` forces `c = 0` (the size condition gives
`0 ≤ c`), where `1` is a near square root (`nsqrtRecursive_base`,
`isNearSquareRoot_one_of_hasSizeCondition`); the step descends to the reduced problem
`⌊n / 4M²⌋` at `⌊c/2⌋` via the scaler `M = 2^⌊(c-1)/2⌋`, and `key_isqrt_lemma` lifts its near
square root back to one for `n` (`nsqrtRecursive_succ`). -/
theorem nsqrtRecursive_correctness {n c : Int} (hsc : hasSizeCondition n c) :
    ∃ a, nsqrtRecursive n c = .ok a ∧ isNearSquareRoot n a := by
  by_cases hc : c ≤ 0
  · -- base: `c ≤ 0` with `0 ≤ c` forces `c = 0`.
    have hc0 : c = 0 := Int.le_antisymm hc hsc.c_nonneg
    subst hc0
    exact ⟨1, nsqrtRecursive_base n hc, isNearSquareRoot_one_of_hasSizeCondition hsc⟩
  · -- step: `k = ⌊(c-1)/2⌋`; the scaler `M = 2^k` is suitable for `n`.
    have hc_pos : 0 < c := Int.not_le.mp hc
    let k := (c - 1).fdiv 2
    let M : Int := 2 ^ k.toNat
    have hM_def : M = 2 ^ ((c - 1).fdiv 2).toNat := rfl
    have hM : isSuitableScaler n M := isSuitableScaler_of_hasSizeCondition hM_def hc_pos hsc
    -- The recursion solves the reduced problem `⌊n / 4M²⌋`, returning a near √ `a`; the step
    -- returns `Ma + ⌊n / 4Ma⌋`, which the key lemma certifies as a near √ of `n`.
    obtain ⟨a, ha_eq, a_near⟩ := nsqrtRecursive_correctness (size_condition_step hM_def hc_pos hsc)
    exact ⟨M * a + n.fdiv (4 * M * a),
           nsqrtRecursive_succ hM_def hc_pos a_near.pos ha_eq,
           key_isqrt_lemma hM a_near⟩
termination_by c.toNat
decreasing_by grind only

/-- Correctness of the recursive monadic integer square root `isqrtRecursive`.

For nonnegative `n` it returns a value `a = ⌊√n⌋` (`isIntegerSquareRoot n a`); for
negative `n` it raises exactly the `ValueError` CPython does. The returns proof
reduces the `do`-block to the `nsqrtRecursive` call characterised by `nsqrtRecursive_correctness`
— establishing en route that none of the `Except` operations ever takes its error
branch for `n ≥ 0` — and closes the `n ≥ 1` case with the final `a-1`/`a`
adjustment (`isNearSquareRoot.toIntegerSquareRoot`), which the recursive source's
`a - 1 if n < a * a else a` already matches verbatim. The contract `isCorrectIsqrt`
is the same one the iterative `isCorrectIsqrt_isqrtIterative` establishes. -/
public theorem isCorrectIsqrt_isqrtRecursive : isCorrectIsqrt isqrtRecursive := by
  refine ⟨?_, ?_⟩
  · -- Nonnegative `n`: the recursion runs, never raises, and returns `⌊√n⌋`.
    intro n hn
    show ∃ a, returns (isqrtRecursive n) a ∧ isIntegerSquareRoot n a
    rcases (Int.lt_or_eq_of_le hn).symm with rfl | hpos
    · -- n = 0: special-cased to 0.
      refine ⟨0, ?_, ?_⟩
      · show isqrtRecursive 0 = .ok 0; unfold isqrtRecursive; rfl
      · show isIntegerSquareRoot 0 0; unfold isIntegerSquareRoot; decide
    · -- 0 < n: the recursion runs and never raises.
      have hn0 : n ≠ 0 := Int.ne_of_gt hpos
      let c := (n.bitLength - 1).fdiv 2
      have hc_def : c = (n.bitLength - 1).fdiv 2 := rfl
      obtain ⟨a, ha_eq, a_near⟩ :=
        nsqrtRecursive_correctness (c := c) (size_condition_initial hpos)
      have hred : isqrtRecursive n = .ok (if n < a * a then a - 1 else a) := by
        unfold isqrtRecursive
        simp only [if_neg (show ¬ n < 0 by omega), if_neg hn0, pure_bind,
          pyFloordiv_eq_ok (show 2 ≠ 0 by decide), ← hc_def]
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
