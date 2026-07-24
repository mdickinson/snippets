/-
Correctness of the iterative monadic integer square root `isqrtIterative`.

Under the near-√ invariant the loop body never raises, so `forIn_pure_of_inv` collapses the whole
`forIn` to a pure `foldl` (`loop_near`); the invariant, indexed by the remaining iteration count,
carries a near square root of the iteration-`s` subproblem and shares the Newton step
(`isNearSquareRoot_newtonLift`) with the recursive proof. `isCorrectIsqrt_isqrtIterative` folds
`isqrtIterative` onto that loop and reads the result off, wrapping it in the `isCorrectIsqrt` contract.
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

/-- A loop that is effect-free under an invariant is a pure fold. If, on every state meeting the
(list-indexed, hence position-aware) invariant `Inv`, the `body` reduces to `pure (.yield (f a b))`
and re-establishes `Inv`, then the whole `forIn` collapses to `pure` of the corresponding `foldl`,
and `Inv` holds of the final state. This is the invariant-carrying analogue of the core lemma
`List.forIn_pure_yield_eq_foldl` (its `Inv := fun _ _ => True` case). -/
theorem forIn_pure_of_inv {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (Inv : List α → β → Prop) (f : α → β → β)
    (L : List α) (init : β) (body : α → β → m (ForInStep β))
    (hinit : Inv L init)
    (hstep : ∀ a L' b, Inv (a :: L') b →
        body a b = pure (ForInStep.yield (f a b)) ∧ Inv L' (f a b)) :
    forIn L init body = pure (L.foldl (fun b a => f a b) init)
      ∧ Inv [] (L.foldl (fun b a => f a b) init) := by
  induction L generalizing init with
  | nil => exact ⟨by simp, hinit⟩
  | cons a L' ih =>
    obtain ⟨hbody, hinv'⟩ := hstep a L' init hinit
    obtain ⟨heq, hfin⟩ := ih (f a init) hinv'
    exact ⟨by rw [List.forIn_cons, hbody, pure_bind, List.foldl_cons]; exact heq,
      by rw [List.foldl_cons]; exact hfin⟩

/-- The reversed `range` peels its largest element off the front. -/
theorem range_reverse_succ (m : Nat) :
    (range (↑(m + 1) : Int)).reverse = ↑m :: (range (↑m : Int)).reverse := by
  rw [Nat.range_eq, Nat.range_eq, List.range_succ, List.map_append, List.reverse_append]
  rfl

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
  rw [show n >>> (2 * c - e - d + 1) = m >>> (d - e + 1) by rw [← Int.shiftRight_add]; congr 1; omega]
  rw [show d - e - 1 = k by omega, show d - e + 1 = k + 2 by omega]
  rfl

/-- One loop iteration as a total function on the raw state: the running approximation is Newton
lifted for the iteration-`s` subproblem and the second component records `p.c >>> s`. This is the
value `loopBody` yields under the loop invariant (see `loopBody_subAt`). -/
def pureStep (p : SizedProblem) (r : LoopState) (s : Nat) : LoopState :=
  ((subAt p s).newtonLift r.fst, ↑(subAt p s).c)

/-- Invariant at depth s. -/
def loopInvariant (p : SizedProblem) (r : LoopState) (s : Nat) : Prop :=
  let ⟨a, d⟩ := r
  isNearSquareRoot (subAt p s).n a ∧ d = ↑(subAt p s).c

/-- Under the loop invariant, loopBody yields the result of applying pureStep. -/
theorem loopBody_subAt (p : SizedProblem)
    {s : Nat} (hs : s < p.height)
    (r : LoopState)
    (hinv : loopInvariant p r (s + 1)) :
    loopBody p.n ↑p.c ↑s r = .ok (ForInStep.yield (pureStep p r s)) := by
  rw [loopBody_eq_ok p.n p.c r hs hinv.1.1 (subAt_c p (s + 1) ▸ hinv.2)]
  rw [pureStep, SizedProblem.newtonLift_eq, subAt_n, subAt_k, subAt_c]

/-- The loop invariant holds initially. -/
theorem loopInvariant_initial (p : SizedProblem) :
    loopInvariant p (1, 0) p.height :=
  ⟨subAt_isNearSquareRoot_one p, by rw [subAt_c, SizedProblem.height, Nat.shiftRight_size_self, Int.cast_ofNat_Int]⟩

/-- Each step preserves the loop invariant. -/
theorem loopInvariant_step (p : SizedProblem)
    {s : Nat} (hs : s < p.height)
    (r : LoopState)
    (hinv : loopInvariant p r (s + 1)) :
    loopInvariant p (pureStep p r s) s := by
  obtain ⟨ha_near, hsnd⟩ := hinv
  refine ⟨subAt_isNearSquareRoot_newtonLift hs ha_near, rfl⟩

/-
Threading a general invariant through a for loop over a reversed range, where each
iteration of the for loop is a pure yield, and that fact depends on the invariant.
-/
theorem reverse_range_zero : (range (0 : Nat)).reverse = [] := by
  rw [Nat.range_eq, List.range_zero, List.map_nil, List.reverse_nil]

theorem reverse_range_succ (m : Nat) : (range ↑(m + 1)).reverse = ↑m :: (range ↑m).reverse := by
  rw [Nat.range_eq, Nat.range_eq, List.range_succ, List.map_append, List.reverse_append]
  rfl

theorem forIn_reverse_range_invariant
    {LoopState : Type}
    (height : Nat)
    (initial : LoopState)
    (step : LoopState -> Nat -> LoopState)
    (body : Int -> LoopState -> PyExcept (ForInStep LoopState))
    (invariant : LoopState -> Nat -> Prop)
    (hinitial : invariant initial height)
    (hstep : ∀ {s : Nat}, s < height → ∀ r : LoopState, invariant r (s + 1) →
      body ↑s r = .ok (ForInStep.yield (step r s)) ∧ invariant (step r s) s) :
    ∃ y : LoopState, forIn (range height).reverse initial body = .ok y ∧ invariant y 0 := by
  induction height generalizing initial with
  | zero => rw [reverse_range_zero]; exact ⟨initial, rfl, hinitial⟩
  | succ height ind_hyp => rw [reverse_range_succ, List.forIn_cons]; exact (hstep (by omega) initial hinitial).1 ▸ (
      ind_hyp (step initial height)
      (hstep (by omega) initial hinitial).2 (fun hs => hstep (by omega)))

/-- The loop never raises and folds to a near square root: driving `loopBody` over the reversed
`range` from `(1, 0)` succeeds with some final state `y`, so feeding the loop's result to any
continuation `g` evaluates to `g y` — the shape the caller needs to push the loop through the rest
of `isqrtIterative`'s `do` block — and the first component `y.fst` is a near square root of `p.n`.
The near-√ invariant — which subsumes `0 < a`, so no shift or division raises — is threaded through
`forIn_pure_of_inv`, indexed by the number `m` of iterations still to run. -/
theorem loop_near (p : SizedProblem) :
    ∃ y : LoopState,
      (∀ g : LoopState → PyExcept Int,
        forIn (range (p.height : Int)).reverse (1, 0) (loopBody p.n ↑p.c) >>= g = g y)
      ∧ isNearSquareRoot p.n y.fst := by
  obtain ⟨heq, hfin⟩ := forIn_pure_of_inv
    (fun (L' : List Int) (r : LoopState) =>
      ∃ m : Nat, m ≤ p.height ∧ L' = (range (↑m : Int)).reverse
        ∧ r.snd = ↑(subAt p m).c ∧ isNearSquareRoot (subAt p m).n r.fst)
    (fun (s : Int) (r : LoopState) => pureStep p r s.toNat)
    (range (↑p.height : Int)).reverse (1, 0) (loopBody p.n ↑p.c)
    ⟨p.height, Nat.le_refl _, rfl, by simp [subAt_c, SizedProblem.height, Nat.shiftRight_size_self],
      subAt_isNearSquareRoot_one p⟩
    (by
      rintro a L' r ⟨m, hm, hL, hd, hnear⟩
      -- The list is nonempty, so `m = k + 1`, and its head is `↑k`.
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
        cases m with
        | zero =>
          simp only [Nat.range_eq, List.range_zero, List.map_nil, List.reverse_nil] at hL
          exact absurd hL (List.cons_ne_nil a L')
        | succ k => exact ⟨k, rfl⟩
      rw [range_reverse_succ] at hL
      obtain ⟨rfl, rfl⟩ := List.cons.inj hL
      have hk : k < p.height := by omega
      have hstep := loopBody_subAt p hk r ⟨hnear, hd⟩
      exact ⟨hstep, k, by omega, rfl, rfl, subAt_isNearSquareRoot_newtonLift hk hnear⟩
    )
  -- The final list is `[]`, forcing `m = 0`; and `subAt p 0 = p`.
  -- `heq : forIn … = pure y` gives the `∀ g` form by `pure_bind`.
  refine ⟨_, fun g => by rw [heq, pure_bind], ?_⟩
  obtain ⟨m, _, hL, _, hnear⟩ := hfin
  obtain rfl : m = 0 := by
    cases m with
    | zero => rfl
    | succ k => rw [range_reverse_succ] at hL; exact (List.cons_ne_nil _ _ hL.symm).elim
  exact isNearSquareRoot_of_subAt hnear

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
      rw [half_dec_bitLength hpos, Nat.bitLength_eq]
      obtain ⟨y, hy_eq, hy_near⟩ := loop_near (.ofPos hpos)
      rw [SizedProblem.height, SizedProblem.c_eq, SizedProblem.ofPos_n] at hy_eq
      rw [SizedProblem.ofPos_n] at hy_near
      exact ⟨_, hy_eq _, isIntegerSquareRoot_of_isNearSquareRoot hy_near⟩
