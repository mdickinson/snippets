module

public import Isqrt.Definitions.IsqrtIterative
public import Isqrt.Definitions.Specification
import Isqrt.Definitions.PythonPrimitives
import Isqrt.Proofs.KeyLemma
import Isqrt.Proofs.SizeConditions
import Isqrt.Proofs.PythonTranslation
import Isqrt.Proofs.SizedProblem
import Isqrt.Proofs.SupportLemmas

public section

/-- One iteration of the monadic loop, as a standalone `Except`-returning step on the
`MProd` state `⟨a, d⟩` (running approximation `a`, previous shift `d`). This is the loop
body of `isqrtIterative` lifted out: it reads `e = d` (the previous shift), recomputes
`d = c >> s`, and returns the new `⟨a, d⟩`. Each `←` is an operation that could raise. -/
private def stepM (c n : Int) (r : MProd Int Int) (s : Int) : PyExcept (MProd Int Int) := do
  let dNew ← pyRshift c s
  let lsh ← pyLshift r.fst (dNew - r.snd - 1)
  let rsh ← pyRshift n (2 * c - r.snd - dNew + 1)
  let q ← pyFloordiv rsh r.fst
  pure ⟨lsh + q, dNew⟩

/-- A `forIn` whose body always yields the result of a monadic step `g` is a `foldlM`
over the same list, specialised to the "always yield" shape the `do` block produces —
this is what lets the proof replace the loop's `forIn` with a `foldlM` it can induct on. -/
private theorem forIn_yield_bind_eq_foldlM {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (g : β → α → m β) (L : List α) (init : β) :
    forIn L init (fun a b => g b a >>= fun b' => pure (ForInStep.yield b')) = L.foldlM g init := by
  simp

/-- Indexed invariant rule for a left `foldlM` over `(List.range L).reverse` in `Except`.
Each step must additionally witness that `g x s` takes its `.ok` branch, so the rule
threads `.ok`-ness through the whole fold alongside the invariant.
Reading `motive i x` as "`x` is a valid `.ok` state with `i` iterations still to run",
the seed lands at `i = L`, the result at `i = 0`, and the conclusion packages both the
`.ok`-ness of the whole fold and the final invariant. -/
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

/-- `stepM`'s `.ok` value, given the loop body's three preconditions discharged: nonneg
shift count `s`, positive running `a = r.fst`, and the two derived shift-amount bounds. -/
private theorem stepM_eq_ok {c n : Int} (r : MProd Int Int) (s : Int)
    (hs_nn : 0 ≤ s) (ha_pos : 0 < r.fst)
    (hK : 0 ≤ c >>> s.toNat - r.snd - 1)
    (hJ : 0 ≤ 2 * c - r.snd - c >>> s.toNat + 1) :
    stepM c n r s = .ok ⟨r.fst <<< (c >>> s.toNat - r.snd - 1).toNat
        + Int.fdiv (n >>> (2 * c - r.snd - c >>> s.toNat + 1).toNat) r.fst,
      c >>> s.toNat⟩ := by
  simp only [stepM, pyRshift_eq_ok hs_nn, Except.ok_bind,
    pyLshift_eq_ok hK, pyRshift_eq_ok hJ,
    pyFloordiv_eq_ok (Int.ne_of_gt ha_pos)]
  rfl

/-- The monadic loop's `foldlM` is `.ok`, and its running approximation is a positive
near square root of `p.n`. A position-indexed `foldlM` invariant whose motive carries the
running `a > 0`, the threaded shift `d = c >> s`, and the near-√ invariant
`isNearSquareRoot (chain s).n a`, where `chain s = p.subAt (c >> s)` is the depth-`c >> s`
subproblem. The problem is bundled as a `SizedProblem`, so `0 ≤ c` and `0 < n` come from the
invariant. -/
private theorem monadicLoop_near (p : SizedProblem) :
    ∃ y : MProd Int Int,
      (range (↑p.c : Int).bitLength).reverse.foldlM (stepM ↑p.c p.n) ⟨1, 0⟩ = .ok y
      ∧ 0 < y.fst ∧ isNearSquareRoot p.n y.fst := by
  obtain ⟨n, c, hsize⟩ := p
  have hn : 0 < n := hsize.pos
  -- The loop runs on `↑c : Int`; its depth at position `s` is the `Nat` `c >> s`, cast back.
  have hcast : ∀ s : Nat, (↑c : Int) >>> s = ↑(c >>> s) := fun s =>
    (Int.natCast_shiftRight c s).symm
  have hhi : ∀ s : Nat, c >>> s ≤ c := fun s => Nat.shiftRight_le c s
  let chain : Nat → SizedProblem := fun s =>
    (⟨n, c, hsize⟩ : SizedProblem).subAt (c >>> s) (hhi s)
  -- Bridge the `range` list to `(List.range L).reverse` with Nat indices.
  have hlist : (range (↑c : Int).bitLength).reverse
      = (List.range (↑c : Int).bitLength.toNat).reverse.map Int.ofNat := by
    rw [show range (↑c : Int).bitLength
          = (List.range (↑c : Int).bitLength.toNat).map Int.ofNat from rfl,
        ← List.map_reverse]
  rw [hlist, List.foldlM_map]
  -- `L = (↑c).bit_length() = natBitLength c`, where `c >> L = 0`.
  have hz : c >>> (↑c : Int).bitLength.toNat = 0 :=
    Nat.shiftRight_eq_zero c _ (by rw [Int.toNat_bitLength_natCast]; exact lt_two_pow_natBitLength c)
  let motive : Nat → MProd Int Int → Prop := fun (s : Nat) (r : MProd Int Int) =>
    0 < r.fst ∧ r.snd = ↑(c >>> s) ∧ isNearSquareRoot (chain s).n r.fst
  have hmotive : motive = fun (s : Nat) (r : MProd Int Int) =>
    0 < r.fst ∧ r.snd = ↑(c >>> s) ∧ isNearSquareRoot (chain s).n r.fst := rfl
  -- Seed at `s = L`: `c >> L = 0`, so the base subproblem `chain L` (value `n >> 2c ∈ [1, 4)`) has
  -- near-√ `1`.
  have hseed : motive (↑c : Int).bitLength.toNat ⟨1, 0⟩ := by
    refine ⟨Int.one_pos, by rw [hz]; rfl, ?_⟩
    show isNearSquareRoot (n >>> (2 * (c - c >>> (↑c : Int).bitLength.toNat))) 1
    rw [hz]
    exact isNearSquareRoot_one_of_hasSizeCondition
      (hasSizeCondition_of_isSizedAt (size_condition_at_depth (Nat.zero_le c) hsize))
  -- Step: one shared Newton lift (`isNearSquareRoot_newtonLift`, the same lemma the recursion uses),
  -- once `descend_subAt` identifies `chain (i+1)` with `descend (chain i)` and the `.ok`-ness of
  -- `stepM` and the Python-shift → subproblem encoding are discharged.
  have hstep : ∀ s, s < (↑c : Int).bitLength.toNat → ∀ x, motive (s + 1) x →
      ∃ y, stepM (↑c) n x (Int.ofNat s) = .ok y ∧ motive s y := by
    intro i hi x hx
    simp only [hmotive] at hx ⊢
    obtain ⟨ha_pos, hx_snd, hx_near⟩ := hx
    -- Nat depths at this level (`c >> i`) and its child (`c >> (i+1) = ⌊(c >> i)/2⌋`).
    rw [Int.toNat_bitLength_natCast] at hi
    have hc_pos : 0 < c := natBitLength_pos_iff.mp (by omega)
    have hdN_pos : 0 < c >>> i :=
      Nat.shiftRight_pos hc_pos (by rw [← natBitLength_sub_one hc_pos]; omega)
    have hdN_le : c >>> i ≤ c := hhi i
    have heN_halve : c >>> (i + 1) = c >>> i / 2 := Nat.shiftRight_succ c i
    have hsi : (Int.ofNat i).toNat = i := Int.toNat_natCast i
    -- The loop's Int shift `c >> i` is `↑(c >> i)`; the threaded `x.snd` is `↑(c >> (i+1))`.
    have hd_new : (↑c : Int) >>> (Int.ofNat i).toNat = ↑(c >>> i) := by
      rw [hsi]; exact hcast i
    -- the IH gives a near-√ of `chain (i+1) = descend (chain i)` (`descend_subAt`, child `⌊(c≫i)/2⌋`)
    have h_child : isNearSquareRoot ((chain i).descend hdN_pos).n x.fst := by
      rw [SizedProblem.descend_subAt]
      show isNearSquareRoot (n >>> (2 * (c - c >>> i / 2))) x.fst
      rw [← heN_halve]
      exact hx_near
    -- assemble: `stepM` succeeds, and its new state is a near-√ at depth `c >> i`
    refine ⟨_, stepM_eq_ok x (Int.ofNat i) (Int.natCast_nonneg i) ha_pos ?_ ?_, ?_, ?_, ?_⟩
    · rw [hd_new, hx_snd]; omega
    · rw [hd_new, hx_snd]; omega
    · -- positivity: `0 < a` survives the left shift; the divided-down remainder is `≥ 0`
      exact Int.add_pos_of_pos_of_nonneg
        (Int.lt_of_lt_of_le ha_pos (Int.le_shiftLeft_of_nonneg (Int.le_of_lt ha_pos)))
        (Int.fdiv_nonneg (Int.le_shiftRight_of_nonneg (Int.le_of_lt hn)) (Int.le_of_lt ha_pos))
    · -- new `d = ↑(c >> i)`
      rw [hd_new]
    · -- near-√ at the new depth: the loop body is the Newton lift of `chain i`, shared with recursion
      rw [hd_new, hx_snd]
      have he1 : (↑(c >>> i) - ↑(c >>> (i + 1)) - 1 : Int).toNat
          = c >>> i - c >>> (i + 1) - 1 := by omega
      have he2 : (2 * (↑c : Int) - ↑(c >>> (i + 1)) - ↑(c >>> i) + 1).toNat
          = 2 * c - c >>> (i + 1) - c >>> i + 1 := by omega
      rw [he1, he2,
        SizedProblem.subAt_body_eq (p := ⟨n, c, hsize⟩) (hhi i) heN_halve hdN_pos]
      exact isNearSquareRoot_newtonLift hdN_pos h_child
  obtain ⟨y, hy_eq, hy_pos, _hy_d, hy_near⟩ :=
    foldlM_reverseRange_invariant motive (fun x s => stepM (↑c) n x (Int.ofNat s))
      (↑c : Int).bitLength.toNat ⟨1, 0⟩ hseed hstep
  -- Result at `s = 0`: `chain 0` is the whole problem — `c >> 0 = c` and `n >> 0 = n`.
  refine ⟨y, hy_eq, hy_pos, ?_⟩
  have hy_near' : isNearSquareRoot (chain 0).n y.fst := hy_near
  have hchain0 : (chain 0).n = n := by
    show n >>> (2 * (c - c >>> 0)) = n
    rw [Nat.shiftRight_zero, Nat.sub_self, Nat.mul_zero, Int.shiftRight_zero]
  rwa [hchain0] at hy_near'

/-- Correctness of the monadic integer square root `isqrtIterative`.

For `n < 0` it raises exactly the `ValueError` CPython does; otherwise it returns `.ok v`
with `v = ⌊√n⌋` (`isIntegerSquareRoot n v`). The proof reduces the `do`-block to the
`foldlM` characterised by `monadicLoop_near` — establishing en route that none of the
`Except` operations ever take their error branch for `n ≥ 0` — and closes the `n ≥ 1`
case with the same final `a-1`/`a` adjustment (`isNearSquareRoot.toIntegerSquareRoot`) as
the recursive and iterative proofs. -/
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
      obtain ⟨y, hy_eq, _hy_pos, hy_near⟩ :=
        monadicLoop_near
          ⟨n, ((n.bitLength - 1).fdiv 2).toNat,
            (Int.toNat_fdiv_bitLength_sub_one hpos).symm ▸ size_condition_initial hpos⟩
      -- The struct's `↑c` is the def's `Int` seed `(n.bitLength - 1) // 2`.
      rw [show ((↑(((n.bitLength - 1).fdiv 2).toNat)) : Int) = (n.bitLength - 1).fdiv 2
            from Int.toNat_of_nonneg (Int.fdiv_bitLength_sub_one_nonneg hn0)] at hy_eq
      have hred : isqrtIterative n = .ok (if n < y.fst * y.fst then y.fst - 1 else y.fst) := by
        unfold isqrtIterative
        simp only [if_neg (show ¬ n < 0 by omega), if_neg hn0, pure_bind,
          pyFloordiv_eq_ok (show (2 : Int) ≠ 0 by decide)]
        rw [Except.ok_bind]
        have key := forIn_yield_bind_eq_foldlM (stepM ((n.bitLength - 1).fdiv 2) n)
          (range ((n.bitLength - 1).fdiv 2).bitLength).reverse ⟨1, 0⟩
        conv at key => lhs; simp only [stepM, bind_assoc, pure_bind]
        rw [key, hy_eq]; rfl
      exact ⟨_, hred, hy_near.toIntegerSquareRoot⟩
  · -- Negative `n`: the first guard raises, short-circuiting the `do` block.
    intro n hn
    show raises (isqrtIterative n) (.valueError "isqrt() argument must be nonnegative")
    have herr : isqrtIterative n
        = .error (.valueError "isqrt() argument must be nonnegative") := by
      unfold isqrtIterative; rw [if_pos hn]; rfl
    exact herr

end
