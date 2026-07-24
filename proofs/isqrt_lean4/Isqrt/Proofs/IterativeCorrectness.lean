/-
Correctness of the iterative monadic integer square root `isqrtIterative`.

The loop drives `loopBody` over the reversed `range p.height`. `loopInvariant` carries a near square
root of the depth-`s` subproblem (`subAt p s`) — which subsumes `0 < a`, so the body never raises —
and shares its Newton step with the recursive proof; `forIn_reverse_range_invariant` threads it to a
final state satisfying the invariant at depth `0`, i.e. a near square root of `p` itself.
`isCorrectIsqrt_isqrtIterative` folds `isqrtIterative` onto that loop and reads the result off,
wrapping it in the `isCorrectIsqrt` contract.
-/

module

public import Isqrt.Definitions.IsqrtIterative
public import Isqrt.Definitions.Specification
import Isqrt.Definitions.PythonPrimitives
import Isqrt.Proofs.KeyLemmaBitwise
import Isqrt.Proofs.NatSize
import Isqrt.Proofs.NearRootSteps
import Isqrt.Proofs.PythonTranslation
import Isqrt.Proofs.SizedProblem
import Isqrt.Proofs.SubAt
import Isqrt.Proofs.SupportLemmas

open scoped Python

/-! ## The main loop -/

/-- The mutable state defined before and updated within the for loop: (a, d). -/
abbrev LoopState := Int × Int

/-- The for-loop body, named. This is definitionally what `isqrtIterative`'s `do`-block desugars to,
so the correctness proof folds the loop into `forIn … (loopBody n c)`. -/
def loopBody (n c : Int) (s : Int) (r : LoopState) : PyExcept (ForInStep LoopState) :=
  let ⟨a, d⟩ := r
  do
  let e := d
  let d ← c >> s
  let a := (← a << (d - e - 1)) + (← (← n >> (2 * c - e - d + 1)) // a)
  pure (ForInStep.yield (a, d))

/--
A single iteration performs a Newton lift of the current approximation
with respect to n >> (2(c - d)) and k = (d - 1) / 2.
-/
theorem loopBody_eq_ok (n : Int) (c : Nat) (r : LoopState) {s : Nat} (hs : s < c.size)
    (ha_pos : 0 < r.fst)
    (hsnd : r.snd = (c >>> (s + 1) : Nat)) :
    let a := r.fst
    let d := c >>> s
    let m := n >>> (2 * (c - d))
    let k := (d - 1) / 2
    loopBody n ↑c ↑s r = .ok (ForInStep.yield ⟨newtonLift m k a, ↑d⟩) := by
  intro a d m k
  let e := c >>> (s + 1)
  have : 0 < d := by rw [← Nat.size_pos, Nat.size_shiftRight]; omega
  have : d ≤ c := Nat.shiftRight_le c s
  have : e = d / 2 := Nat.shiftRight_succ c s
  rw [loopBody]
  rw [pyRshift_ok_bind]
  rw [show ((c : Int) >>> s - r.snd - 1) = ((d - e - 1) : Nat) by rw [hsnd]; norm_cast; omega]
  rw [pyLshift_ok_bind]
  rw [show (2 * (c : Int) - r.snd - (c : Int) >>> s + 1) = ((2 * ↑c - e - d + 1) : Nat) by
    rw [hsnd]; norm_cast; omega]
  rw [pyRshift_ok_bind, pyFloordiv_ok_bind (by omega)]
  rw [show n >>> (2 * c - e - d + 1) = m >>> (d - e + 1) by
    rw [← Int.shiftRight_add]; congr 1; omega]
  rw [show d - e - 1 = k by omega, show d - e + 1 = k + 2 by omega]
  rfl

/-- One loop iteration as a total function on the raw state: the running approximation is Newton
lifted for the iteration-`s` subproblem and the second component records `p.c >>> s`. This is the
value `loopBody` yields under the loop invariant (see `loopInvariant_step`). -/
def pureStep (p : SizedProblem) (r : LoopState) (s : Nat) : LoopState :=
  ((subAt p s).newtonLift r.fst, ↑(subAt p s).c)

/-- Invariant at depth s. -/
def loopInvariant (p : SizedProblem) (r : LoopState) (s : Nat) : Prop :=
  let ⟨a, d⟩ := r
  isNearSquareRoot (subAt p s).n a ∧ d = ↑(subAt p s).c

/-- The loop invariant holds initially. -/
theorem loopInvariant_initial (p : SizedProblem) :
    loopInvariant p (1, 0) p.height :=
  ⟨subAt_nsqrt_base p,
    by rw [subAt_c, SizedProblem.height, Nat.shiftRight_size_self, Int.cast_ofNat_Int]⟩

/-- Under the loop invariant, loopBody is a pure yield and the new invariant holds. -/
theorem loopInvariant_step (p : SizedProblem)
    {s : Nat} (hs : s < p.height)
    (r : LoopState)
    (hinv : loopInvariant p r (s + 1)) :
    loopBody p.n ↑p.c ↑s r = .ok (ForInStep.yield (pureStep p r s)) ∧
    loopInvariant p (pureStep p r s) s := by
  refine ⟨?_, subAt_nsqrt_lift hs hinv.1, rfl⟩
  rw [loopBody_eq_ok p.n p.c r hs hinv.1.1 (subAt_c p (s + 1) ▸ hinv.2)]
  rw [pureStep, SizedProblem.newtonLift_eq, subAt_n, subAt_k, subAt_c]

/-- Correctness of `isqrtIterative`: for nonnegative `n` it returns `⌊√n⌋`, and for negative `n` it
raises the same `ValueError` as CPython. -/
public theorem isCorrectIsqrt_isqrtIterative : isCorrectIsqrt isqrtIterative := by
  refine ⟨?_, ?_⟩ <;> intro n hn
  · -- Negative `n`: the first guard raises, short-circuiting the `do` block.
    rw [isqrtIterative, if_pos hn]; rfl
  · -- Nonnegative `n`: the loop runs, never raises, and returns `⌊√n⌋`.
    rcases (Int.lt_or_eq_of_le hn).symm with rfl | hpos
    · -- n = 0: special-cased to 0.
      exact ⟨0, rfl, by unfold isIntegerSquareRoot; decide⟩
    · -- 0 < n: the loop runs and never raises.
      rw [isqrtIterative, if_neg (by omega), if_neg (by omega)]
      rw [half_dec_bitLength hpos, Int.bitLength_natCast]
      let p : SizedProblem := .ofPos hpos
      obtain ⟨y, hy_eq, hy_inv⟩ := forIn_reverse_range_invariant p.height (1, 0)
        (pureStep p) (loopBody p.n ↑p.c) (loopInvariant p)
        (loopInvariant_initial p) (loopInvariant_step p)
      rw [SizedProblem.height, SizedProblem.c_eq, SizedProblem.ofPos_n] at hy_eq
      exact ⟨
        _,
        hy_eq _,
        isIntegerSquareRoot_of_isNearSquareRoot
          (SizedProblem.ofPos_n hpos ▸ nsqrt_of_subAt_zero hy_inv.1)
      ⟩
