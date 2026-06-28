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
import Isqrt.Proofs.SizedProblem
import Isqrt.Proofs.FDivLemmas

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
theorem nsqrtRecursive_succ {n a M : Int} {c : Nat}
    (hM : M = 2 ^ ((c - 1) / 2)) (hc : 0 < c) (ha : 0 < a)
    (h_sub : nsqrtRecursive (n.fdiv (4 * M ^ 2)) ↑(c / 2) = .ok a) :
    nsqrtRecursive n ↑c = .ok (M * a + n.fdiv (4 * M * a)) := by
  have hc' : (0 : Int) < ↑c := by exact_mod_cast hc
  -- `kk` is the def's `Int` recursion depth `(↑c - 1) // 2`; its `.toNat` is the scaler exponent.
  let kk : Int := (↑c - 1 : Int).fdiv 2
  have hkk_def : kk = (↑c - 1 : Int).fdiv 2 := rfl
  have kk_nn : 0 ≤ kk := Int.fdiv_nonneg (by omega) (by omega)
  have hkk : kk.toNat = (c - 1) / 2 := Int.toNat_fdiv_pred_two hc
  have h2k2 : (2 * kk + 2).toNat = 2 * kk.toNat + 2 := by omega
  have hk2 : (kk + 2).toNat = kk.toNat + 2 := by omega
  have hcdiv : (↑c : Int).fdiv 2 = ↑(c / 2) := by
    rw [show ((2 : Int)) = ((2 : Nat) : Int) from rfl, Int.fdiv_natCast_natCast]
  have hMk : M = 2 ^ kk.toNat := by rw [hM, hkk]
  -- The subcall's `4M²` denominator is the Python shift `2^(2k+2)`.
  rw [hMk, four_mul_two_pow_sq kk.toNat] at h_sub
  -- Thread the `.ok` branches to the shift-form body, then rewrite it to `Ma + ⌊n / 4Ma⌋`.
  have hred : nsqrtRecursive n ↑c
      = .ok (a * 2 ^ kk.toNat + (n.fdiv (2 ^ (kk.toNat + 2))).fdiv a) := by
    unfold nsqrtRecursive
    rw [if_neg (Int.not_le.mpr hc')]
    simp only [pyFloordiv_eq_ok (show (2 : Int) ≠ 0 by decide), ← hkk_def, Except.ok_bind,
      pyRshift_eq_ok (show (0 : Int) ≤ 2 * kk + 2 by omega), h2k2, hcdiv, h_sub,
      pyLshift_eq_ok kk_nn, pyRshift_eq_ok (show (0 : Int) ≤ kk + 2 by omega), hk2,
      pyFloordiv_eq_ok (Int.ne_of_gt ha)]
    rfl
  rw [hred, key_isqrt_body_eq ha hMk]

/-- The recursive auxiliary returns a near square root of `p.n` and **never raises**, for any
`SizedProblem p`.

The argument is one `SizedProblem` — the value, its recursion level, and the size invariant
bundled — so the recursion threads a single descending problem. Each case supplies the goal's two
facts, the value the function returns and that it is a near square root. The base case `p.c ≤ 0`
forces `p.c = 0` (the invariant gives `0 ≤ p.c`), where `1` is a near square root
(`nsqrtRecursive_base`, `isNearSquareRoot_one_of_hasSizeCondition`); the step solves the descended
problem `p.descend` and lifts its near square root back with `p.newtonLift`
(`isNearSquareRoot_newtonLift`, `nsqrtRecursive_succ`). -/
theorem nsqrtRecursive_correctness (p : SizedProblem) :
    ∃ a, nsqrtRecursive p.n ↑p.c = .ok a ∧ isNearSquareRoot p.n a := by
  by_cases hc : p.c = 0
  · -- base: at `p.c = 0`, `1` is a near square root.
    exact ⟨1, nsqrtRecursive_base p.n (by omega),
      isNearSquareRoot_one_of_hasSizeCondition (hc ▸ p.hsc)⟩
  · -- step: solve the descended problem, lift its near square root back.
    have hc_pos : 0 < p.c := Nat.pos_of_ne_zero hc
    obtain ⟨a, ha_eq, a_near⟩ := nsqrtRecursive_correctness (p.descend hc_pos)
    exact ⟨p.newtonLift a, nsqrtRecursive_succ rfl hc_pos a_near.pos ha_eq,
      isNearSquareRoot_newtonLift hc_pos a_near⟩
termination_by p.c
decreasing_by simp only [SizedProblem.descend]; omega

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
      obtain ⟨a, ha_eq, a_near⟩ :=
        nsqrtRecursive_correctness ⟨n, ((n.bitLength - 1).fdiv 2).toNat, size_condition_initial hpos⟩
      -- The struct's `↑c` is the def's `Int` seed `(n.bitLength - 1) // 2`.
      rw [show ((↑(((n.bitLength - 1).fdiv 2).toNat)) : Int) = (n.bitLength - 1).fdiv 2
            from Int.toNat_of_nonneg (isqrt_c_nonneg hn0)] at ha_eq
      have hred : isqrtRecursive n = .ok (if n < a * a then a - 1 else a) := by
        unfold isqrtRecursive
        simp only [if_neg (show ¬ n < 0 by omega), if_neg hn0, pure_bind,
          pyFloordiv_eq_ok (show (2 : Int) ≠ 0 by decide)]
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
