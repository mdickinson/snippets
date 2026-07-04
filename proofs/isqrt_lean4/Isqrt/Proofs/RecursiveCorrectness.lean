/-
Correctness of the recursive monadic integer square root `isqrtRecursive`.

`nsqrtRecursive_base` and `nsqrtRecursive_succ` reduce each recursion step to its returned value
(discharging the `.ok`-ness of every Python operation), so `nsqrtRecursive_correctness` reads as the
mathematical argument alone; `isCorrectIsqrt_isqrtRecursive` wraps it in the `isCorrectIsqrt`
contract.
-/

module

public import Isqrt.Definitions.IsqrtRecursive
public import Isqrt.Definitions.Specification
import Isqrt.Definitions.PythonPrimitives
import Isqrt.Proofs.SizeConditions
import Isqrt.Proofs.PythonTranslation
import Isqrt.Proofs.SizedProblem
import Isqrt.Proofs.NearRootSteps
import Isqrt.Proofs.SupportLemmas

/-- The recursion bottoms out at `c ≤ 0`, returning `1` regardless of `n`. -/
theorem nsqrtRecursive_base (n : Int) {c : Int} (hc : c ≤ 0) :
    nsqrtRecursive n c = .ok 1 := by
  unfold nsqrtRecursive; rw [if_pos hc]; rfl

/-- One unfolding at `0 < c`, in `SizedProblem`'s shift form: a successful subcall on the descended
value returning `0 < a` makes every Python operation take its `.ok` branch, and the step returns the
Newton lift. -/
theorem nsqrtRecursive_succ {n a : Int} {c : Nat} (hc : 0 < c) (ha : 0 < a)
    (h_sub : nsqrtRecursive (n >>> (2 * ((c - 1) / 2) + 2)) ↑(c / 2) = .ok a) :
    nsqrtRecursive n ↑c
      = .ok (a <<< ((c - 1) / 2) + (n >>> ((c - 1) / 2 + 2)) / a) := by
  have hc' : (0 : Int) < ↑c := by exact_mod_cast hc
  -- `kk` is the def's `Int` recursion depth `(↑c - 1) // 2`; its `.toNat` is the shift amount.
  let kk : Int := (↑c - 1 : Int) / 2
  have hkk_def : kk = (↑c - 1 : Int) / 2 := rfl
  have kk_nn : 0 ≤ kk := Int.ediv_nonneg (by omega) (by omega)
  have hkk : kk.toNat = (c - 1) / 2 := by subst kk; omega
  have h2k2 : (2 * kk + 2).toNat = 2 * kk.toNat + 2 := by omega
  have hk2 : (kk + 2).toNat = kk.toNat + 2 := by omega
  have hcdiv : (↑c : Int) / 2 = ↑(c / 2) := by omega
  -- Match the subcall's shift amount `(2*kk+2).toNat` to `h_sub`'s `2⌊(c-1)/2⌋+2`.
  rw [← hkk] at h_sub
  -- Thread the `.ok` branches; the body comes out already in the lift's shift form.
  have hred : nsqrtRecursive n ↑c
      = .ok (a <<< kk.toNat + (n >>> (kk.toNat + 2)) / a) := by
    unfold nsqrtRecursive
    rw [if_neg (Int.not_le.mpr hc')]
    simp only [pyFloordiv_eq_ok (show (0 : Int) < 2 by decide), ← hkk_def, Except.ok_bind,
      pyRshift_eq_ok (show (0 : Int) ≤ 2 * kk + 2 by omega), h2k2, hcdiv, h_sub,
      pyLshift_eq_ok kk_nn, pyRshift_eq_ok (show (0 : Int) ≤ kk + 2 by omega), hk2,
      pyFloordiv_eq_ok ha]
    rfl
  rw [hred, hkk]

/-- The recursive auxiliary returns a near square root of `p.n` and never raises, for any
`SizedProblem p`: the base case (`p.c = 0`) returns `1`; the step solves `p.descend` and lifts it
back with `p.newtonLift`. -/
theorem nsqrtRecursive_correctness (p : SizedProblem) :
    ∃ a, nsqrtRecursive p.n ↑p.c = .ok a ∧ isNearSquareRoot p.n a := by
  by_cases hc : p.c = 0
  · -- base: at `p.c = 0`, `1` is a near square root.
    exact ⟨1, nsqrtRecursive_base p.n (by omega),
      isNearSquareRoot_one_of_hasSizeCondition (hc ▸ p.hsc)⟩
  · -- step: solve the descended problem, lift its near square root back.
    have hc_pos : 0 < p.c := Nat.pos_of_ne_zero hc
    obtain ⟨a, ha_eq, a_near⟩ := nsqrtRecursive_correctness (p.descend hc_pos)
    -- `(p.descend).n` and `p.newtonLift a` are the shift forms `nsqrtRecursive_succ` speaks, so the
    -- IH `ha_eq` and the returned value land definitionally — no shift↔multiplicative bridge here.
    exact ⟨p.newtonLift a, nsqrtRecursive_succ hc_pos a_near.1 ha_eq,
      isNearSquareRoot_newtonLift hc_pos a_near⟩
termination_by p.c
decreasing_by simp only [SizedProblem.descend]; omega

/-- Correctness of `isqrtRecursive`: for nonnegative `n` it returns `⌊√n⌋`, and for negative `n` it
raises the same `ValueError` as CPython. -/
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
        nsqrtRecursive_correctness
          ⟨n, (n.toNat.size - 1) / 2, size_condition_initial hpos⟩

      -- The struct's `↑c` is the def's `Int` seed `(n.bitLength - 1) // 2`.
      have hred : isqrtRecursive n = .ok (if n < a * a then a - 1 else a) := by
        unfold isqrtRecursive
        simp only [if_neg (show ¬ n < 0 by omega), if_neg hn0, pure_bind,
          pyFloordiv_eq_ok (show (0 : Int) < 2 by decide)]
        have hsize : 0 < n.toNat.size := Nat.size_pos.mpr (by omega)
        rw [Except.ok_bind, Int.bitLength_eq hn,
          show ((n.toNat.size : Int) - 1) / 2 = ((n.toNat.size - 1) / 2 : Nat) from by omega,
          ha_eq]
        rfl
      exact ⟨_, hred, isIntegerSquareRoot_of_isNearSquareRoot a_near⟩
  · -- Negative `n`: the first guard raises, short-circuiting the `do` block.
    intro n hn
    show raises (isqrtRecursive n) (.valueError "isqrt() argument must be nonnegative")
    have herr : isqrtRecursive n
        = .error (.valueError "isqrt() argument must be nonnegative") := by
      unfold isqrtRecursive; rw [if_pos hn]; rfl
    exact herr
