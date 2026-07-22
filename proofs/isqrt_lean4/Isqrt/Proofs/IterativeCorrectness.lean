/-
Correctness of the iterative monadic integer square root `isqrtIterative`.

The loop's `foldlM` is mirrored by `augmentedAfter`, a recursion over the subproblem chain whose
state (`AugmentedLoopState`) carries the near-√ invariant alongside the running approximation,
sharing the Newton step (`isNearSquareRoot_newtonLift`) with the recursive proof; `monadicLoop_near`
reads the result off the final augmented state and `isCorrectIsqrt_isqrtIterative` wraps it in the
`isCorrectIsqrt` contract.
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

/-- A `forIn` whose body always yields the result of a monadic step `g` equals `foldlM g` over the
same list. -/
theorem forIn_yield_bind_eq_foldlM {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (g : β → α → m β) (L : List α) (init : β) :
    forIn L init (fun a b => g b a >>= fun b' => pure (ForInStep.yield b')) = L.foldlM g init := by
  simp

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
abbrev LoopState := MProd Int Int

/-- The loop state immediately before entering the for loop. -/
def initialLoopState : LoopState := ⟨1, 0⟩

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

/-- The state on exiting the for loop. -/
def finalLoopState (p : SizedProblem) : PyExcept LoopState :=
  (range (p.c.size : Int)).reverse.foldlM (stepM p.n ↑p.c) initialLoopState

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

/-- Loop state augmented with the near-√ invariant at iteration `s`. The second component `p.c >>> s`
is pinned by the index, so `forget` recovers it without storing it. -/
private structure AugmentedLoopState (p : SizedProblem) (s : Nat) where
  a : Int
  a_near : isNearSquareRoot (subAt p s).n a

/-- Initial augmented loop state. -/
def augmentedInitial {p : SizedProblem} : AugmentedLoopState p p.c.size :=
  ⟨1, isNearSquareRoot_one subAt_irreducible⟩

/-- One iteration of the augmented for loop. -/
def augmentedStep {p : SizedProblem} {s : Nat} (hs : s < p.c.size)
    (r : AugmentedLoopState p (s + 1)) : AugmentedLoopState p s := by
  obtain ⟨a_old, a_near_old⟩ := r
  refine ⟨(subAt p s).newtonLift a_old, ?_⟩
  apply isNearSquareRoot_newtonLift (subAt_reducible p s hs)
  rw [descend_subAt]
  exact a_near_old

/-- The augmented loop state after iteration `s`. -/
def augmentedAfter (p : SizedProblem) (s : Nat) (hs : s ≤ p.c.size) : AugmentedLoopState p s :=
  if h : s = p.c.size then
    h ▸ augmentedInitial
  else
    augmentedStep (by omega) (augmentedAfter p (s + 1) (by omega))

/-- The final augmented state. -/
def augmentedFinal (p : SizedProblem) : AugmentedLoopState p 0 := augmentedAfter p 0 (by omega)

/-- Below the top level, iteration `s` is one `augmentedStep` on iteration `s+1`. -/
theorem augmentedAfter_of_lt (p : SizedProblem) {s : Nat} (hs : s < p.c.size) :
    augmentedAfter p s (Nat.le_of_lt hs) = augmentedStep hs (augmentedAfter p (s + 1) hs) := by
  rw [augmentedAfter, dif_neg (Nat.ne_of_lt hs)]

/-- Extraction of loop state from augmented loop state; the second component is `p.c >>> s`. -/
def forget {p : SizedProblem} {s : Nat} (r : AugmentedLoopState p s) : LoopState :=
  ⟨r.a, ↑(p.c >>> s)⟩

/-- Initial states coincide. -/
theorem initialAugmented_eq_initialLoopState {p : SizedProblem} :
    forget (augmentedInitial : AugmentedLoopState p p.c.size) = initialLoopState := by
  show (⟨1, ↑(p.c >>> p.c.size)⟩ : LoopState) = ⟨1, 0⟩
  rw [Nat.shiftRight_size_self]; rfl

/-- One `stepM` on a forgotten state equals the forget of one `augmentedStep`. -/
theorem stepM_forget (p : SizedProblem) {s : Nat} (hs : s < p.c.size)
    (r : AugmentedLoopState p (s + 1)) :
    stepM p.n ↑p.c (forget r) ↑s = .ok (forget (augmentedStep hs r)) := by
  rw [stepM_subAt p hs _ r.a_near.1 rfl]; rfl

/-- Running the loop's `foldlM` from iteration `s` reproduces the augmented recursion: each Python
step mirrors one `augmentedStep`, so the fold lands on the final augmented state. -/
theorem foldl_augmentedAfter (p : SizedProblem) :
    ∀ (s : Nat) (hs : s ≤ p.c.size),
      (List.range s).reverse.foldlM (fun (x : LoopState) (a : Nat) => stepM p.n ↑p.c x ↑a)
          (forget (augmentedAfter p s hs))
        = .ok (forget (augmentedFinal p)) := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    have hcons : (List.range (s + 1)).reverse = s :: (List.range s).reverse := by
      rw [List.range_succ, List.reverse_append]; rfl
    rw [hcons]
    simp only [List.foldlM_cons]
    rw [stepM_forget p hs (augmentedAfter p (s + 1) hs),
      ← augmentedAfter_of_lt p hs, Except.ok_bind]
    exact ih (Nat.le_of_lt hs)

/-- The loop's `foldlM` computes exactly the final augmented state. -/
theorem finalLoopState_eq_augmentedFinal (p : SizedProblem) :
    finalLoopState p = .ok (forget (augmentedFinal p)) := by
  rw [finalLoopState, Nat.range_eq, ← List.map_reverse, List.foldlM_map]
  rw [show initialLoopState = forget (augmentedAfter p p.c.size (Nat.le_refl _)) by
        rw [augmentedAfter, dif_pos rfl]; exact initialAugmented_eq_initialLoopState.symm]
  exact foldl_augmentedAfter p p.c.size (Nat.le_refl _)

/-- The loop's `foldlM` is `.ok`, and its running approximation is a near square root of `p.n`. -/
theorem monadicLoop_near (p : SizedProblem) :
    ∃ y : LoopState,
      finalLoopState p = .ok y
      ∧ isNearSquareRoot p.n y.fst := by
  refine ⟨forget (augmentedFinal p), finalLoopState_eq_augmentedFinal p, ?_⟩
  -- The near-√ invariant is carried by the augmented state; at iteration `0` its subproblem is `p`.
  have h := (augmentedFinal p).a_near
  rwa [subAt_zero] at h

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
      obtain ⟨y, hy_eq, hy_near⟩ := monadicLoop_near (.ofPos hpos)
      rw [finalLoopState] at hy_eq
      simp only [SizedProblem.ofPos_n, SizedProblem.c_eq] at hy_eq hy_near
      -- The struct's `↑c` is the def's `Int` seed `(n.bitLength - 1) // 2`.
      have hred : isqrtIterative n = .ok (if n < y.fst * y.fst then y.fst - 1 else y.fst) := by
        rw [isqrtIterative, Int.bitLength_eq hn]
        rw [if_neg (by omega), pure_bind, if_neg (by omega), pure_bind]
        rw [pyFloordiv_ok_bind (by decide)]
        simp only [pure_bind]
        rw [← initialLoopState]
        have hsize : 0 < n.toNat.size := Nat.size_pos.mpr (by omega)
        let c := (n.toNat.size - 1) / 2
        rw [show ((n.toNat.size : Int) - 1) / 2 = c by omega]
        rw [Nat.bitLength_eq]
        have key := forIn_yield_bind_eq_foldlM (stepM n ↑c)
          (range (c.size : Int)).reverse initialLoopState
        conv at key => lhs; simp only [stepM, bind_assoc, pure_bind]
        rw [key, hy_eq]
        rfl
      exact ⟨_, hred, isIntegerSquareRoot_of_isNearSquareRoot hy_near⟩
  · -- Negative `n`: the first guard raises, short-circuiting the `do` block.
    intro n hn
    show raises (isqrtIterative n) (.valueError "isqrt() argument must be nonnegative")
    have herr : isqrtIterative n
        = .error (.valueError "isqrt() argument must be nonnegative") := by
      unfold isqrtIterative; rw [if_pos hn]; rfl
    exact herr
