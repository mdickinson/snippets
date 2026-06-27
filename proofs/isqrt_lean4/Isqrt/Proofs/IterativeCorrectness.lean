module

meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.Positivity
public import Isqrt.Definitions.IsqrtIterative
public import Isqrt.Definitions.Specification
import Isqrt.Definitions.PythonPrimitives
import Isqrt.Proofs.KeyLemma
import Isqrt.Proofs.SizeConditions
import Isqrt.Proofs.PythonPrimitivesLemmas

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
    (hK : 0 ≤ Int.fdiv c (2 ^ s.toNat) - r.snd - 1)
    (hJ : 0 ≤ 2 * c - r.snd - Int.fdiv c (2 ^ s.toNat) + 1) :
    stepM c n r s = .ok ⟨r.fst * 2 ^ (Int.fdiv c (2 ^ s.toNat) - r.snd - 1).toNat
        + Int.fdiv (Int.fdiv n (2 ^ (2 * c - r.snd - Int.fdiv c (2 ^ s.toNat) + 1).toNat)) r.fst,
      Int.fdiv c (2 ^ s.toNat)⟩ := by
  simp only [stepM, pyRshift_eq_ok hs_nn, Except.ok_bind,
    pyLshift_eq_ok hK, pyRshift_eq_ok hJ,
    pyFloordiv_eq_ok (ne_of_gt ha_pos)]
  rfl

/-- The monadic loop's `foldlM` is `.ok`, and its running approximation is a positive
near square root of `n`. A position-indexed `foldlM` invariant whose motive carries the
running `a > 0`, the threaded shift `d = c >> s`, and the near-√ invariant
`isNearSquareRoot (subproblem n c (c >> s)) a`. -/
private theorem monadicLoop_near {n c : Int} (hc : 0 ≤ c) (hn : 0 < n)
    (hsc : hasSizeCondition n c) :
    ∃ y : MProd Int Int, (range c.bitLength).reverse.foldlM (stepM c n) ⟨1, 0⟩ = .ok y
      ∧ 0 < y.fst ∧ isNearSquareRoot n y.fst := by
  -- Bridge the `range` list to `(List.range L).reverse` with Nat indices.
  have hlist : (range c.bitLength).reverse
      = (List.range c.bitLength.toNat).reverse.map Int.ofNat := by
    rw [show range c.bitLength = (List.range c.bitLength.toNat).map Int.ofNat from rfl,
        ← List.map_reverse]
  rw [hlist, List.foldlM_map]
  -- `c >> L = 0`, where `L = c.bit_length()`.
  have hz : Int.fdiv c (2 ^ c.bitLength.toNat) = 0 := fdiv_two_pow_bitLength_eq_zero hc
  set motive : Nat → MProd Int Int → Prop := fun (s : Nat) (r : MProd Int Int) =>
    0 < r.fst ∧ r.snd = Int.fdiv c (2 ^ s)
      ∧ isNearSquareRoot (subproblem n c (Int.fdiv c (2 ^ s))) r.fst with hmotive
  -- Seed at `s = L`: `c >> L = 0`, so the base subproblem `⌊n/4^c⌋ ∈ [1, 4)` has near-√ `1`.
  have hseed : motive c.bitLength.toNat ⟨1, 0⟩ := by
    refine ⟨one_pos, hz.symm, ?_⟩
    rw [hz]
    exact isNearSquareRoot_one_of_hasSizeCondition (size_condition_at_depth (d := 0) le_rfl hc hsc)
  -- Step: one shared Newton refinement (`isNearSquareRoot_subproblem_step`), once the
  -- `.ok`-ness of `stepM` and the Python-shift → `subproblem` encoding are discharged.
  have hstep : ∀ s, s < c.bitLength.toNat → ∀ x, motive (s + 1) x →
      ∃ y, stepM c n x (Int.ofNat s) = .ok y ∧ motive s y := by
    intro i hi x hx
    simp only [hmotive] at hx ⊢
    set sZ : Int := (i : Int)
    have hs_nn : 0 ≤ sZ := by positivity
    have hs_lt : sZ < c.bitLength := by have := Int.bitLength_nonneg c; omega
    have hsi : sZ.toNat = i := Int.toNat_natCast i
    have hsi1 : (sZ + 1).toNat = i + 1 := by omega
    set d_new := Int.fdiv c (2 ^ i) with hd_new_def
    set d_old := Int.fdiv c (2 ^ (i + 1)) with hd_old_def
    set a_old := x.fst
    obtain ⟨ha_old_pos, hx_snd, hx_near⟩ := hx
    -- depth bookkeeping: `d_new = c >> i` climbs from its child `d_old = ⌊d_new/2⌋`
    have hd_new_fdiv : d_new = Int.fdiv c (2 ^ sZ.toNat) := by rw [hsi]
    have hd_old_fdiv : d_old = Int.fdiv c (2 ^ (sZ + 1).toNat) := by rw [hsi1]
    have hd_old_nonneg : 0 ≤ d_old := by rw [hd_old_def]; exact Int.fdiv_nonneg hc (by positivity)
    have hd_new_le : d_new ≤ c := by rw [hd_new_def]; exact Int.fdiv_le_self _ hc
    have hK : 0 ≤ d_new - d_old - 1 := by
      rw [hd_new_fdiv]; exact fdiv_two_pow_lshift_nonneg hc hs_nn hs_lt hd_old_fdiv
    have hd_new_pos : 0 < d_new := by omega
    have h_halve : d_old = d_new.fdiv 2 := by
      rw [hd_old_fdiv, hd_new_fdiv]; exact fdiv_two_pow_succ c sZ hs_nn
    have hk_eq : (d_new - 1).fdiv 2 = d_new - d_old - 1 := by
      rw [h_halve, Int.fdiv_eq_ediv_of_nonneg (d_new - 1) (by norm_num : (0 : Int) ≤ 2),
          Int.fdiv_eq_ediv_of_nonneg d_new (by norm_num : (0 : Int) ≤ 2)]
      omega
    have hk_nn : (0 : Int) ≤ (d_new - 1).fdiv 2 := Int.fdiv_nonneg (by omega) (by norm_num)
    have hJ : 0 ≤ 2 * c - d_old - d_new + 1 := by
      have hd_old_le : d_old ≤ c := by rw [hd_old_fdiv]; exact Int.fdiv_le_self _ hc
      omega
    set M := (2 : Int) ^ ((d_new - 1).fdiv 2).toNat with hM_def
    -- the loop body's new `a`, in Python shift form, is the Newton combine on `subproblem n c d_new`
    have hX : a_old * 2 ^ (d_new - d_old - 1).toNat
            + Int.fdiv (Int.fdiv n (2 ^ (2 * c - d_old - d_new + 1).toNat)) a_old
          = M * a_old + (subproblem n c d_new).fdiv (4 * M * a_old) := by
      -- rewrite the body's `n`-divisor into the `subproblem n c d_new`-divisor shape
      -- `key_isqrt_body_eq` expects (factoring out `4 ^ (c - d_new)`)
      have hbridge : Int.fdiv n (2 ^ (2 * c - d_old - d_new + 1).toNat)
          = (subproblem n c d_new).fdiv (2 ^ ((d_new - 1).fdiv 2 + 2).toNat) := by
        unfold subproblem
        rw [Int.fdiv_fdiv_eq_fdiv_mul n (by positivity) (by positivity)]
        congr 1
        rw [show (4 : Int) = 2 ^ 2 by norm_num]
        simp only [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [show (d_new - d_old - 1).toNat = ((d_new - 1).fdiv 2).toNat from by rw [hk_eq], hbridge]
      exact key_isqrt_body_eq hk_nn ha_old_pos hM_def
    -- assemble: `stepM` succeeds, and its new state is a near-√ at depth `d_new`
    refine ⟨_, stepM_eq_ok x sZ hs_nn ha_old_pos ?_ ?_, ?_, ?_, ?_⟩
    · rw [hsi, hx_snd]; exact hK
    · rw [hsi, hx_snd]; exact hJ
    · -- positivity of the new `a`
      exact add_pos_of_pos_of_nonneg
        (mul_pos ha_old_pos (by positivity))
        (Int.fdiv_nonneg (Int.fdiv_nonneg hn.le (by positivity)) ha_old_pos.le)
    · -- new `d = c >> i`
      rfl
    · -- near-√ at the new depth, via the shared Newton step from the child `d_old = ⌊d_new/2⌋`
      rw [hx_snd]
      show isNearSquareRoot (subproblem n c d_new) (a_old * 2 ^ (d_new - d_old - 1).toNat
          + Int.fdiv (Int.fdiv n (2 ^ (2 * c - d_old - d_new + 1).toNat)) a_old)
      rw [hX]
      exact isNearSquareRoot_subproblem_step hM_def hsc hd_new_pos hd_new_le (h_halve ▸ hx_near)
  obtain ⟨y, hy_eq, hy_pos, _hy_d, hy_near⟩ :=
    foldlM_reverseRange_invariant motive (fun x s => stepM c n x (Int.ofNat s))
      c.bitLength.toNat ⟨1, 0⟩ hseed hstep
  -- Result at `s = 0`: `c >> 0 = c`, and `subproblem n c c = n`, so a near-√ of `n`.
  refine ⟨y, hy_eq, hy_pos, ?_⟩
  simpa [pow_zero, Int.fdiv_one, subproblem_self] using hy_near

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
    rcases eq_or_lt_of_le hn with rfl | hpos
    · -- n = 0: special-cased to 0.
      refine ⟨0, ?_, ?_⟩
      · show isqrtIterative 0 = .ok 0; unfold isqrtIterative; norm_num; rfl
      · show isIntegerSquareRoot 0 0; unfold isIntegerSquareRoot; norm_num
    · -- 0 < n: the loop runs and never raises.
      have hn0 : n ≠ 0 := ne_of_gt hpos
      obtain ⟨y, hy_eq, _hy_pos, hy_near⟩ :=
        monadicLoop_near (c := (n.bitLength - 1).fdiv 2) (isqrt_c_nonneg hn0) hpos
          (size_condition_initial hpos)
      have hred : isqrtIterative n = .ok (if n < y.fst * y.fst then y.fst - 1 else y.fst) := by
        conv_lhs => unfold isqrtIterative
        simp only [if_neg (show ¬ n < 0 by omega), if_neg hn0, pure_bind,
          pyFloordiv_eq_ok (show (2 : Int) ≠ 0 by norm_num)]
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
