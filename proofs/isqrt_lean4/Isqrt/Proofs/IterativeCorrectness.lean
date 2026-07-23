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
import Isqrt.Proofs.NatSize
import Isqrt.Proofs.NearRootSteps
import Isqrt.Proofs.PythonTranslation
import Isqrt.Proofs.SizedProblem
import Isqrt.Proofs.SupportLemmas



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

/-! ## The subproblem chain -/

/-- `descend`'s value in terms of the level `c`: it shifts `n` right by `2(c − ⌊c/2⌋)`, the form the
subproblem chain descends by (equivalently `descend_n`'s `2k+2`). -/
theorem descend_n_of_c (p : SizedProblem) (hp : p.reducible) :
    (p.descend hp).n = p.n >>> (2 * (p.c - p.c / 2)) := by
  rw [SizedProblem.descend_n, SizedProblem.c_eq, SizedProblem.k_eq]
  have : 2 < p.n.toNat.size := Int.lt_size.mpr (p.four_le_n.mp hp)
  congr 1; omega

theorem subAt_pos (p : SizedProblem) (i : Nat) : 0 < p.n >>> (2 * (p.c - (p.c >>> i))) := by
  apply Int.shiftRight_pos
  have : 2 * (p.c - p.c >>> i) ≤ 2 * p.c := by grind only
  apply Nat.lt_of_le_of_lt this
  rw [p.c_eq]
  have : 0 < p.n.toNat.size := by
    rw [Nat.size_pos]
    have := p.n_pos
    omega
  omega

/-- The iteration-`i` subproblem descending from `p`: value `p.n >>> 2(c - c>>>i)` at level
`c >>> i`, carrying the inherited size invariant. -/
def subAt (p : SizedProblem) (i : Nat) : SizedProblem :=
  SizedProblem.ofPos (subAt_pos p i)

/-- The iteration-`i` subproblem's value in shift form. -/
theorem subAt_n (p : SizedProblem) (i : Nat) :
    (subAt p i).n = p.n >>> (2 * (p.c - p.c >>> i)) := by
  unfold subAt; rw [SizedProblem.ofPos_n]

/-- The iteration-`i` subproblem's level is `c >>> i`. -/
theorem subAt_c (p : SizedProblem) (i : Nat) : (subAt p i).c = p.c >>> i := by
  grind only [subAt, SizedProblem.ofPos_n, SizedProblem.c_eq, Int.size_shiftRight, Nat.shiftRight_le]

/-- The iteration-`i` subproblem's `k` is `((c >>> i) - 1)/2`. -/
theorem subAt_k (p : SizedProblem) (i : Nat) : (subAt p i).k = (p.c >>> i - 1) / 2 := by
  rw [SizedProblem.k_of_c, subAt_c]

/-- Chain top: iteration `0` is the whole problem. -/
theorem subAt_zero (p : SizedProblem) : subAt p 0 = p := by
  apply SizedProblem.eq_of_n_eq
  simp only [subAt, SizedProblem.ofPos_n, Nat.shiftRight_zero, Nat.sub_self, Nat.mul_zero, Int.shiftRight_zero]

/-- The subproblem at depth `c.size` is irreducible. -/
theorem subAt_irreducible {p : SizedProblem} : (subAt p p.c.size).irreducible := by
  rw [SizedProblem.irreducible_iff, subAt_c]
  exact Nat.shiftRight_size_self

/-- Subproblems below depth `c.size` are reducible. -/
theorem subAt_reducible (p : SizedProblem) (i : Nat) (hi : i < p.c.size) :
    (subAt p i).reducible := by
  rw [SizedProblem.reducible_iff, subAt_c]; exact Nat.shiftRight_pos hi

/-- Chain step: descending iteration `i` gives iteration `i+1`. -/
theorem descend_subAt {p : SizedProblem} {i : Nat} (hp : (subAt p i).reducible) :
    (subAt p i).descend hp = subAt p (i + 1) := by
  apply SizedProblem.eq_of_n_eq
  rw [descend_n_of_c]
  rw [subAt_c, subAt_n, subAt_n]
  rw [← Int.shiftRight_add, ← Nat.shiftRight_succ]
  congr 1
  have : p.c >>> i ≤ p.c := by apply Nat.shiftRight_le
  have : p.c >>> (i + 1) ≤ p.c >>> i := by rw [Nat.shiftRight_add]; apply Nat.shiftRight_le
  omega

/-! ## The main loop -/

/-- The mutable state defined before and updated within the for loop: (a, d). -/
abbrev LoopState := Int × Int

/-- The computation represented by one iteration of the for loop. -/
def stepM (n c : Int) (r : LoopState) (s : Int) : PyExcept LoopState :=
  have a := r.fst
  have d := r.snd
  have e := d
  do
  let d ← pyRshift c s
  let lsh ← pyLshift a (d - e - 1)
  let rsh ← pyRshift n (2 * c - e - d + 1)
  let q ← pyFloordiv rsh a
  let a := lsh + q
  pure ⟨a, d⟩

/--
A single iteration performs a Newton lift of the current approximation
with respect to n >> (2(c - d)) and k = (d - 1) / 2.
-/
theorem stepM_eq_ok (n : Int) (c : Nat) (r : LoopState)
    {s : Nat} (hs : s < c.size)
    (ha_pos : 0 < r.fst)
    (hsnd : r.snd = (c >>> (s + 1) : Nat)) :
    let a := r.fst
    let d := c >>> s
    let m := n >>> (2 * (c - d))
    let k := (d - 1) / 2
    stepM n ↑c r ↑s = .ok ⟨a <<< k + (m >>> (k + 2)) / a, ↑d⟩ := by
  intro a d m k
  let e := c >>> (s + 1)
  have : 0 < d := by rw [← Nat.size_pos, Nat.size_shiftRight]; omega
  have : d ≤ c := Nat.shiftRight_le c s
  have : e = d / 2 := Nat.shiftRight_succ c s
  rw [stepM]
  rw [pyRshift_ok_bind]
  rw [show ((c : Int) >>> s - r.snd - 1) = ((d - e - 1) : Nat) by rw [hsnd]; norm_cast; omega]
  rw [pyLshift_ok_bind]
  rw [show (2 * (c : Int) - r.snd - (c : Int) >>> s + 1) = ((2 * ↑c - e - d + 1) : Nat) by
    rw [hsnd]; norm_cast; omega]
  rw [pyRshift_ok_bind, pyFloordiv_ok_bind (by omega)]
  rw [show n >>> (2 * c - e - d + 1) = m >>> (d - e + 1) by rw [← Int.shiftRight_add]; congr 1; omega]
  rw [show d - e - 1 = k by omega, show d - e + 1 = k + 2 by omega]
  rfl

/-- One `stepM` at position `i` succeeds and returns the iteration-`i` subproblem's Newton lift —
the iterative analogue of `nsqrtRecursive_succ`. -/
theorem stepM_subAt
    (p : SizedProblem)
    {s : Nat} (hs : s < p.c.size)
    (r : LoopState)
    (ha : 0 < r.fst)
    (hsnd : r.snd = ↑(p.c >>> (s + 1))) :
    stepM p.n ↑p.c r ↑s
      = .ok ⟨(subAt p s).newtonLift r.fst, ↑(p.c >>> s)⟩ := by
  rw [stepM_eq_ok p.n p.c r hs ha hsnd]
  rw [SizedProblem.newtonLift_eq, subAt_n, subAt_k]

/-- One loop iteration as a total function on the raw state: the running approximation is Newton
lifted for the iteration-`s` subproblem and the second component records `p.c >>> s`. This is
`stepM`'s `.ok` value under the loop invariant (see `stepM_subAt`). -/
def pureStep (p : SizedProblem) (r : LoopState) (s : Nat) : LoopState :=
  ((subAt p s).newtonLift r.fst, ↑(p.c >>> s))

/-- The for-loop body, named. This is definitionally what `isqrtIterative`'s `do`-block desugars to,
so the correctness proof folds the loop into `forIn … (loopBody n c)`. -/
abbrev loopBody (n c : Int) (s : Int) (r : LoopState) : PyExcept (ForInStep LoopState) := do
  let d ← pyRshift c s
  let lsh ← pyLshift r.fst (d - r.snd - 1)
  let rsh ← pyRshift n (2 * c - r.snd - d + 1)
  let q ← pyFloordiv rsh r.fst
  pure (ForInStep.yield (lsh + q, d))

/-- The loop never raises and folds to a near square root: driving `loopBody` over the reversed
`range` from `(1, 0)` succeeds, and the first component of the result is a near square root of `p.n`.
The near-√ invariant — which subsumes `0 < a`, so no shift or division raises — is threaded through
`forIn_pure_of_inv`, indexed by the number `m` of iterations still to run. -/
theorem loop_near (p : SizedProblem) :
    ∃ y : LoopState,
      forIn (range (↑p.c.size : Int)).reverse ((1, 0) : LoopState) (loopBody p.n ↑p.c) = pure y
      ∧ isNearSquareRoot p.n y.fst := by
  obtain ⟨heq, hfin⟩ := forIn_pure_of_inv
    (fun (L' : List Int) (r : LoopState) =>
      ∃ m : Nat, m ≤ p.c.size ∧ L' = (range (↑m : Int)).reverse
        ∧ r.snd = ↑(p.c >>> m) ∧ isNearSquareRoot (subAt p m).n r.fst)
    (fun (s : Int) (r : LoopState) => pureStep p r s.toNat)
    (range (↑p.c.size : Int)).reverse (1, 0) (loopBody p.n ↑p.c)
    ⟨p.c.size, Nat.le_refl _, rfl, by simp [Nat.shiftRight_size_self],
      isNearSquareRoot_one subAt_irreducible⟩
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
      have hk : k < p.c.size := by omega
      have hstepM := stepM_subAt p hk r hnear.1 hd
      refine ⟨?_, k, by omega, rfl, rfl, ?_⟩
      · -- Purity: the body is `stepM`, which succeeds, wrapped for `forIn`.
        have hbridge : loopBody p.n ↑p.c ↑k r
            = stepM p.n ↑p.c r ↑k >>= fun r' => pure (ForInStep.yield r') := by
          simp only [loopBody, stepM, bind_assoc, pure_bind]
        rw [hbridge, hstepM, Except.ok_bind]; rfl
      · -- The near-√ invariant is preserved by the Newton lift.
        show isNearSquareRoot (subAt p k).n ((subAt p k).newtonLift r.fst)
        apply isNearSquareRoot_newtonLift (subAt_reducible p k hk)
        rw [descend_subAt]; exact hnear)
  -- The final list is `[]`, forcing `m = 0`; and `subAt p 0 = p`.
  refine ⟨_, heq, ?_⟩
  obtain ⟨m, _, hL, _, hnear⟩ := hfin
  obtain rfl : m = 0 := by
    cases m with
    | zero => rfl
    | succ k => rw [range_reverse_succ] at hL; exact (List.cons_ne_nil _ _ hL.symm).elim
  rwa [subAt_zero] at hnear

/-- Correctness of `isqrtIterative`: for nonnegative `n` it returns `⌊√n⌋`, and for negative `n` it
raises the same `ValueError` as CPython. -/
public theorem isCorrectIsqrt_isqrtIterative : isCorrectIsqrt isqrtIterative := by
  refine ⟨?_, ?_⟩
  · -- Nonnegative `n`: the loop runs, never raises, and returns `⌊√n⌋`.
    intro n hn
    show ∃ a, returns (isqrtIterative n) a ∧ isIntegerSquareRoot n a
    rcases (Int.lt_or_eq_of_le hn).symm with rfl | hpos
    · -- n = 0: special-cased to 0.
      exact ⟨0, by rfl, by unfold isIntegerSquareRoot; decide⟩
    · -- 0 < n: the loop runs and never raises.
      have hn0 : n ≠ 0 := Int.ne_of_gt hpos
      obtain ⟨y, hy_eq, hy_near⟩ := loop_near (.ofPos hpos)
      simp only [SizedProblem.ofPos_n, SizedProblem.c_eq] at hy_eq hy_near
      refine ⟨_, ?_, isIntegerSquareRoot_of_isNearSquareRoot hy_near⟩
      -- Reduce `isqrtIterative` to the named loop, then read off `pure y`.
      show isqrtIterative n = .ok (if n < y.fst * y.fst then y.fst - 1 else y.fst)
      rw [isqrtIterative, Int.bitLength_eq hn]
      simp only [if_neg (show ¬ n < 0 by omega), if_neg (show ¬ n = 0 by omega)]
      rw [pyFloordiv_ok_bind (by decide)]
      -- The def's `Int` seed `(n.bitLength - 1) // 2` is the struct's `↑p.c`.
      have hsize : 0 < n.toNat.size := Nat.size_pos.mpr (by omega)
      rw [show ((n.toNat.size : Int) - 1) / 2 = ((n.toNat.size - 1) / 2 : Nat) by omega,
        Nat.bitLength_eq, hy_eq, pure_bind]
      rfl
  · -- Negative `n`: the first guard raises, short-circuiting the `do` block.
    intro n hn
    show raises (isqrtIterative n) (.valueError "isqrt() argument must be nonnegative")
    have herr : isqrtIterative n
        = .error (.valueError "isqrt() argument must be nonnegative") := by
      unfold isqrtIterative; rw [if_pos hn]; rfl
    exact herr
