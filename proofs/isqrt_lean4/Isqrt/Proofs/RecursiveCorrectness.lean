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
import Isqrt.Proofs.NatSize
import Isqrt.Proofs.NearRootSteps
import Isqrt.Proofs.PythonTranslation
import Isqrt.Proofs.SizedProblem
import Isqrt.Proofs.SupportLemmas

/-- The recursion bottoms out at `c ≤ 0`, returning `1` regardless of `n`. -/
theorem nsqrtRecursive_base {p : SizedProblem} (hp : p.irreducible) :
    nsqrtRecursive p.n ↑p.c = .ok 1 := by
  unfold nsqrtRecursive
  have hc_neg : p.c ≤ (0 : Int) :=
    Int.natCast_nonpos_iff.mpr (SizedProblem.irreducible_iff.mp hp)
  rw [if_pos hc_neg]; rfl

/-- One unfolding at `0 < c`, in raw shift form: a successful subcall on the descended value
returning `0 < a` makes every Python operation take its `.ok` branch, and the step returns the Newton
lift. -/
theorem nsqrtRecursive_succ_shift
    {n : Int} {c : Nat} (hc : 0 < c) {a : Int} (a_pos : 0 < a):
    let k := (c - 1) / 2
    nsqrtRecursive (n >>> (2 * k + 2)) ↑(c / 2) = .ok a →
    nsqrtRecursive n ↑c = .ok (a <<< k + (n >>> (k + 2)) / a) := by
  intro k nsr_inner
  rw [nsqrtRecursive, if_neg (by omega)]
  rw [pyFloordiv_ok_bind (by decide)]
  rw [show (2 * (((c : Int) - 1) / 2) + 2) = (2 * k + 2 : Nat) by omega]
  rw [pyRshift_ok_bind]
  rw [show ((c : Int) / 2) = ↑(c / 2) by omega]
  rw [nsr_inner, Except.ok_bind]
  rw [show (((c : Int) - 1) / 2) = k by omega]
  rw [pyLshift_ok_bind]
  norm_cast
  rw [pyRshift_ok_bind]
  rw [pyFloordiv_ok_bind (by omega)]
  rfl

/-- The recursive step in `SizedProblem` terms: a solved descendant lifts back to `p` via
`newtonLift`. -/
theorem nsqrtRecursive_succ
    {p : SizedProblem} (hp : p.reducible) {a : Int} (ha : 0 < a) :
    nsqrtRecursive (p.descend hp).n ↑(p.descend hp).c = .ok a →
    nsqrtRecursive p.n ↑p.c = .ok (p.newtonLift a) := by
  intro h_sub
  rw [p.newtonLift_eq, p.k_of_c]
  apply nsqrtRecursive_succ_shift (SizedProblem.reducible_iff.mp hp) ha
  rw [← p.k_of_c, ← p.descend_n hp, ← p.descend_c hp]
  exact h_sub

/-- The recursive auxiliary returns a near square root of `p.n` and never raises, for any
`SizedProblem p`: the base case (`p.c = 0`) returns `1`; the step solves `p.descend` and lifts it
back with `p.newtonLift`. -/
theorem nsqrtRecursive_correctness (p : SizedProblem) :
    ∃ a, nsqrtRecursive p.n ↑p.c = .ok a ∧ isNearSquareRoot p.n a := by
  by_cases hp : p.reducible
  · -- step: solve the descended problem, lift its near square root back.
    obtain ⟨a, ha_eq, a_near⟩ := nsqrtRecursive_correctness (p.descend hp)
    exact ⟨p.newtonLift a, nsqrtRecursive_succ hp a_near.1 ha_eq,
      isNearSquareRoot_newtonLift hp a_near⟩
  · -- base: at `p.c = 0`, `1` is a near square root.
    exact ⟨1, nsqrtRecursive_base hp, isNearSquareRoot_one hp⟩
termination_by p.n.toNat.size
decreasing_by exact p.descend_lt hp

/-- Correctness of `isqrtRecursive`: for nonnegative `n` it returns `⌊√n⌋`, and for negative `n` it
raises the same `ValueError` as CPython. -/
public theorem isCorrectIsqrt_isqrtRecursive : isCorrectIsqrt isqrtRecursive := by
  constructor
  · -- Nonnegative `n`: the recursion runs, never raises, and returns `⌊√n⌋`.
    intro n hn
    rcases (Int.lt_or_eq_of_le hn).symm with rfl | hpos
    · -- n = 0: special-cased to 0.
      exact ⟨0, by rfl, by unfold isIntegerSquareRoot; decide⟩
    · -- 0 < n: the recursion runs and never raises.
      obtain ⟨a, ha_eq, a_near⟩ := nsqrtRecursive_correctness (.ofPos hpos)
      simp only [SizedProblem.ofPos_n, SizedProblem.c_eq] at ha_eq a_near
      have hred : isqrtRecursive n = .ok (if n < a * a then a - 1 else a) := by
        rw [isqrtRecursive, if_neg (by omega), if_neg (by omega)]
        rw [half_dec_bitLength hpos, ha_eq]
        rfl
      exact ⟨_, hred, isIntegerSquareRoot_of_isNearSquareRoot a_near⟩
  · -- Negative `n`: the first guard raises, short-circuiting the `do` block.
    intro n hn
    rw [isqrtRecursive, if_pos hn]; rfl
