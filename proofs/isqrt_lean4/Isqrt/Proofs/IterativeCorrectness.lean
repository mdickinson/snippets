/-
Correctness of the iterative monadic integer square root `isqrtIterative`.

`monadicLoop_near` characterises the loop as a `foldlM` and runs a position-indexed invariant that
carries the running approximation up the chain of subproblems, sharing the Newton step
(`isNearSquareRoot_newtonLift`) with the recursive proof; `isCorrectIsqrt_isqrtIterative` wraps it
in the `isCorrectIsqrt` contract.
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

public section

/-- One loop iteration as a standalone `Except`-returning step on the state `⟨a, d⟩` (running
approximation `a`, previous shift `d`). -/
private def stepM (n c : Int) (r : MProd Int Int) (s : Int) : PyExcept (MProd Int Int) := do
  let dNew ← pyRshift c s
  let lsh ← pyLshift r.fst (dNew - r.snd - 1)
  let rsh ← pyRshift n (2 * c - r.snd - dNew + 1)
  let q ← pyFloordiv rsh r.fst
  pure ⟨lsh + q, dNew⟩

/-- A `forIn` whose body always yields the result of a monadic step `g` equals `foldlM g` over the
same list. -/
private theorem forIn_yield_bind_eq_foldlM {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (g : β → α → m β) (L : List α) (init : β) :
    forIn L init (fun a b => g b a >>= fun b' => pure (ForInStep.yield b')) = L.foldlM g init := by
  simp

/-- Indexed invariant rule for a left `foldlM` over `(List.range L).reverse` in `Except`: each step
threads `.ok`-ness alongside the invariant `motive` (index `i` = iterations still to run). -/
private theorem foldlM_reverseRange_invariant {A : Type} (motive : Nat → A → Prop)
    (g : A → Nat → PyExcept A) :
    ∀ (L : Nat) (init : A), motive L init →
      (∀ s, s < L → ∀ x, motive (s + 1) x → ∃ y, g x s = .ok y ∧ motive s y) →
      ∃ y, (List.range L).reverse.foldlM g init = .ok y ∧ motive 0 y := by
  intro L
  induction L with
  | zero => intro init hinit _; exact ⟨init, rfl, hinit⟩
  | succ L ih =>
    intro init hinit hstep
    have hcons : (List.range (L + 1)).reverse = L :: (List.range L).reverse := by
      rw [List.range_succ, List.reverse_append]; rfl
    rw [hcons, List.foldlM_cons]
    obtain ⟨y1, hy1_eq, hy1_mot⟩ := hstep L (Nat.lt_succ_self L) init hinit
    rw [hy1_eq, Except.ok_bind]
    exact ih y1 hy1_mot (fun s hs x hmot => hstep s (Nat.lt_succ_of_lt hs) x hmot)

/-- `stepM`'s `.ok` value, given nonneg shift `s`, positive `r.fst`, and the two shift-amount
bounds. -/
private theorem stepM_eq_ok {n c : Int} (r : MProd Int Int) (s : Int)
    (hs_nn : 0 ≤ s) (ha_pos : 0 < r.fst)
    (hK : 0 ≤ c >>> s.toNat - r.snd - 1)
    (hJ : 0 ≤ 2 * c - r.snd - c >>> s.toNat + 1) :
    stepM n c r s = .ok ⟨r.fst <<< (c >>> s.toNat - r.snd - 1).toNat
        + (n >>> (2 * c - r.snd - c >>> s.toNat + 1).toNat) / r.fst,
      c >>> s.toNat⟩ := by
  simp only [stepM, pyRshift_eq_ok hs_nn, Except.ok_bind,
    pyLshift_eq_ok hK, pyRshift_eq_ok hJ,
    pyFloordiv_eq_ok ha_pos]
  rfl

/-! ## The subproblem chain -/

private theorem descend_n'' (p : SizedProblem) (hp : p.reducible) :
    (p.descend hp).n = p.n >>> (2 * (p.c - p.c / 2)) := by
  rw [SizedProblem.descend_n, SizedProblem.c_eq, SizedProblem.k_eq]
  have : 2 < p.n.toNat.size := Int.lt_size.mpr (p.four_le_n.mp hp)
  congr 1; omega

private theorem subAt_pos (p : SizedProblem) (i : Nat) : 0 < p.n >>> (2 * (p.c - (p.c >>> i))) := by
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
private def subAt (p : SizedProblem) (i : Nat) : SizedProblem :=
  SizedProblem.ofPos (subAt_pos p i)

/-- The iteration-`i` subproblem's value in shift form. -/
private theorem subAt_n (p : SizedProblem) (i : Nat) :
    (subAt p i).n = p.n >>> (2 * (p.c - p.c >>> i)) := by
  unfold subAt; rw [SizedProblem.ofPos_n]

/-- The iteration-`i` subproblem's level is `c >>> i`. -/
private theorem subAt_c (p : SizedProblem) (i : Nat) : (subAt p i).c = p.c >>> i := by
  grind only [subAt, SizedProblem.ofPos_c, Int.size_shiftRight, Nat.shiftRight_le, p.c_eq]

/-- Chain top: iteration `0` is the whole problem. -/
private theorem subAt_zero (p : SizedProblem) : subAt p 0 = p := by
  apply SizedProblem.eq_of_n_eq
  simp only [subAt, SizedProblem.ofPos_n, Nat.shiftRight_zero, Nat.sub_self, Nat.mul_zero, Int.shiftRight_zero]

/-- Chain step: descending iteration `i` gives iteration `i+1`. -/
private theorem descend_subAt (p : SizedProblem) (i : Nat) (hp : (subAt p i).reducible) :
    (subAt p i).descend hp = subAt p (i + 1) := by
  apply SizedProblem.eq_of_n_eq
  rw [descend_n'']
  rw [subAt_c, subAt_n, subAt_n]
  rw [← Int.shiftRight_add, ← Nat.shiftRight_succ]
  congr 1
  have : p.c >>> i ≤ p.c := by apply Nat.shiftRight_le
  have : p.c >>> (i + 1) ≤ p.c >>> i := by rw [Nat.shiftRight_add]; apply Nat.shiftRight_le
  omega

/-- The decoded loop body at position `i` is the iteration-`i` subproblem's Newton lift. -/
private theorem subAt_body_eq (p : SizedProblem) (i : Nat) (a : Int) (hd_pos : 0 < p.c >>> i) :
    a <<< (p.c >>> i - p.c >>> (i + 1) - 1)
        + (p.n >>> (2 * p.c - p.c >>> (i + 1) - p.c >>> i + 1)) / a
      = (subAt p i).newtonLift a := by
  simp only [SizedProblem.newtonLift_eq, subAt_n, ← Int.shiftRight_add, SizedProblem.k_eq]
  rw [Int.size_shiftRight]
  have : (p.n.toNat.size - 2 * (p.c - p.c >>> i) - 3) / 4 =
      ((p.n.toNat.size - 1) / 2 - (p.c - p.c >>> i) - 1) / 2 := by omega
  rw [this]
  rw [← p.c_eq]
  have : (p.c >>> i ≤ p.c) := Nat.shiftRight_le _ _
  have : (p.c - (p.c - p.c >>> i)) = (p.c >>> i) := by omega
  rw [this]
  rw [Nat.shiftRight_succ]
  grind only

/-- One `stepM` at position `i` succeeds and returns the iteration-`i` subproblem's Newton lift —
the iterative analogue of `nsqrtRecursive_succ`. -/
private theorem stepM_subAt (p : SizedProblem) {i : Nat} (r : MProd Int Int)
    (hd_pos : 0 < p.c >>> i) (ha : 0 < r.fst) (hsnd : r.snd = ↑(p.c >>> (i + 1))) :
    stepM p.n (↑p.c) r (Int.ofNat i)
      = .ok ⟨(subAt p i).newtonLift r.fst, ↑(p.c >>> i)⟩ := by
  -- Decode the loop's Int shift `↑c >>> i` to the Nat `↑(c >>> i)`, and record the child halving.
  have hsi : (Int.ofNat i).toNat = i := Int.toNat_natCast i
  have hd_new : (↑p.c : Int) >>> (Int.ofNat i).toNat = ↑(p.c >>> i) := by
    rw [hsi]; exact (Int.natCast_shiftRight p.c i).symm
  have heN_halve : p.c >>> (i + 1) = p.c >>> i / 2 := Nat.shiftRight_succ p.c i
  have hd_le : p.c >>> i ≤ p.c := Nat.shiftRight_le p.c i
  have he_le : p.c >>> (i + 1) ≤ p.c := Nat.shiftRight_le p.c (i + 1)
  -- Every Python op takes its `.ok` branch: the two shift amounts are nonnegative, `r.fst` positive.
  have hK : 0 ≤ (↑p.c : Int) >>> (Int.ofNat i).toNat - r.snd - 1 := by
    rw [hd_new, hsnd, heN_halve]; omega
  have hJ : 0 ≤ 2 * (↑p.c : Int) - r.snd - (↑p.c : Int) >>> (Int.ofNat i).toNat + 1 := by
    rw [hd_new, hsnd]; omega
  rw [stepM_eq_ok r (Int.ofNat i) (Int.natCast_nonneg i) ha hK hJ, hsnd]
  -- Decode the two shift amounts to `Nat`, then recognise the body as the subproblem's Newton lift.
  have he1 : ((↑p.c : Int) >>> (Int.ofNat i).toNat - ↑(p.c >>> (i + 1)) - 1).toNat
      = p.c >>> i - p.c >>> (i + 1) - 1 := by rw [hd_new]; omega
  have he2 : (2 * (↑p.c : Int) - ↑(p.c >>> (i + 1)) - (↑p.c : Int) >>> (Int.ofNat i).toNat + 1).toNat
      = 2 * p.c - p.c >>> (i + 1) - p.c >>> i + 1 := by rw [hd_new]; omega
  rw [he1, he2, hd_new, subAt_body_eq p i r.fst hd_pos]

/-- The loop's `foldlM` is `.ok`, and its running approximation is a near square root of `p.n`. -/
private theorem monadicLoop_near (p : SizedProblem) :
    ∃ y : MProd Int Int,
      (range (↑p.c : Int).bitLength).reverse.foldlM (stepM p.n ↑p.c) ⟨1, 0⟩ = .ok y
      ∧ isNearSquareRoot p.n y.fst := by
  -- The chain of subproblems descending from the whole problem; `chain s` sits at level `c >>> s`.
  let chain : Nat → SizedProblem := subAt p
  -- Bridge the `range` list to `(List.range L).reverse` with Nat indices.
  have hlist : (range (↑p.c : Int).bitLength).reverse
      = (List.range (↑p.c : Int).bitLength.toNat).reverse.map Int.ofNat := by
    rw [show range (↑p.c : Int).bitLength
          = (List.range (↑p.c : Int).bitLength.toNat).map Int.ofNat from rfl,
        ← List.map_reverse]
  rw [hlist, List.foldlM_map]
  -- `c >> bit_length(c) = 0`: shifting past all of `c`'s bits.
  have hz : p.c >>> (↑p.c : Int).bitLength.toNat = 0 := by
    rw [Int.bitLength_eq (Int.natCast_nonneg p.c), Int.toNat_natCast, Int.toNat_natCast]
    exact Nat.shiftRight_size_self
  let motive : Nat → MProd Int Int → Prop := fun (s : Nat) (r : MProd Int Int) =>
    r.snd = ↑(p.c >>> s) ∧ isNearSquareRoot (chain s).n r.fst
  -- Seed at `s = L`: `c >> L = 0`, so the base subproblem `chain L` (value `n >> 2c ∈ [1, 4)`) has
  -- near-√ `1`.
  have hseed : motive (↑p.c : Int).bitLength.toNat ⟨1, 0⟩ := by
    refine ⟨by rw [hz]; rfl, ?_⟩
    apply isNearSquareRoot_one (chain _)
    rw [SizedProblem.irreducible]
    rw [SizedProblem.reducible_iff, Nat.not_lt, Nat.le_zero_eq, Int.bitLength_eq (by omega)]
    simp only [Int.toNat_natCast]
    rw [subAt_c]
    apply Nat.shiftRight_size_self
  -- Step: `stepM_subAt` runs one mechanical step to the iteration-`i` subproblem's Newton lift; its
  -- near-√-ness is the shared lift `isNearSquareRoot_newtonLift`, exactly as the recursion does.
  have hstep : ∀ s, s < (↑p.c : Int).bitLength.toNat → ∀ x, motive (s + 1) x →
      ∃ y, stepM p.n (↑p.c) x (Int.ofNat s) = .ok y ∧ motive s y := by
    intro i hi x hx
    obtain ⟨hx_snd, hx_near⟩ := hx
    rw [Int.bitLength_eq (by omega), Int.toNat_natCast, Int.toNat_natCast] at hi
    have hdN_pos : 0 < p.c >>> i := Nat.shiftRight_pos hi
    -- The IH gives a near-√ of `chain (i+1) = descend (chain i)`.
    have hdp : (chain i).reducible := by
      rw [SizedProblem.reducible_iff]; rw [subAt_c];exact hdN_pos
    have h_child : isNearSquareRoot ((chain i).descend hdp).n x.fst := by
      rw [descend_subAt]; exact hx_near
    exact ⟨_, stepM_subAt p x hdN_pos hx_near.1 hx_snd,
      rfl, isNearSquareRoot_newtonLift (chain i) hdp h_child⟩
  obtain ⟨y, hy_eq, _hy_d, hy_near⟩ :=
    foldlM_reverseRange_invariant motive (fun x s => stepM p.n (↑p.c) x (Int.ofNat s))
      (↑p.c : Int).bitLength.toNat ⟨1, 0⟩ hseed hstep
  -- Result at `s = 0`: `chain 0` is the whole problem `p` (`subAt_zero`).
  refine ⟨y, hy_eq, ?_⟩
  have hchain0 : (chain 0).n = p.n := by
    show (subAt p 0).n = p.n
    rw [subAt_zero]
  rwa [hchain0] at hy_near

/-- Correctness of `isqrtIterative`: for nonnegative `n` it returns `⌊√n⌋`, and for negative `n` it
raises the same `ValueError` as CPython. -/
theorem isCorrectIsqrt_isqrtIterative : isCorrectIsqrt isqrtIterative := by
  refine ⟨?_, ?_⟩
  · -- Nonnegative `n`: the loop runs, never raises, and returns `⌊√n⌋`.
    intro n hn
    show ∃ a, returns (isqrtIterative n) a ∧ isIntegerSquareRoot n a
    rcases (Int.lt_or_eq_of_le hn).symm with rfl | hpos
    · -- n = 0: special-cased to 0.
      refine ⟨0, ?_, ?_⟩
      · show isqrtIterative 0 = .ok 0; unfold isqrtIterative; simp only [reduceIte]; rfl
      · show isIntegerSquareRoot 0 0; unfold isIntegerSquareRoot; decide
    · -- 0 < n: the loop runs and never raises.
      have hn0 : n ≠ 0 := Int.ne_of_gt hpos
      obtain ⟨y, hy_eq, hy_near⟩ :=
        monadicLoop_near (.ofPos hpos)
      simp only [SizedProblem.ofPos_n, SizedProblem.ofPos_c] at hy_eq hy_near
      -- The struct's `↑c` is the def's `Int` seed `(n.bitLength - 1) // 2`.
      have hred : isqrtIterative n = .ok (if n < y.fst * y.fst then y.fst - 1 else y.fst) := by
        unfold isqrtIterative
        simp only [if_neg (show ¬ n < 0 by omega), if_neg hn0, pure_bind,
          pyFloordiv_eq_ok (show (0 : Int) < 2 by decide)]
        have key := forIn_yield_bind_eq_foldlM (stepM n ((n.bitLength - 1) / 2))
          (range ((n.bitLength - 1) / 2).bitLength).reverse ⟨1, 0⟩
        conv at key => lhs; simp only [stepM, bind_assoc, pure_bind]
        have hsize : 0 < n.toNat.size := Nat.size_pos.mpr (by omega)
        rw [Except.ok_bind, key, Int.bitLength_eq hn,
          show ((n.toNat.size : Int) - 1) / 2 = ((n.toNat.size - 1) / 2 : Nat) from by omega,
          hy_eq]
        rfl
      exact ⟨_, hred, isIntegerSquareRoot_of_isNearSquareRoot hy_near⟩
  · -- Negative `n`: the first guard raises, short-circuiting the `do` block.
    intro n hn
    show raises (isqrtIterative n) (.valueError "isqrt() argument must be nonnegative")
    have herr : isqrtIterative n
        = .error (.valueError "isqrt() argument must be nonnegative") := by
      unfold isqrtIterative; rw [if_pos hn]; rfl
    exact herr

end
