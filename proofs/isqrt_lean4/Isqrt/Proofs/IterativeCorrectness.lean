import Isqrt.Definitions.Iterative
import Isqrt.Definitions.Specification
import Isqrt.Proofs.SpecificationLemmas
import Isqrt.Proofs.KeyLemma
import Isqrt.Proofs.SizeConditions
import Isqrt.Proofs.PythonOpsLemmas
import Isqrt.Proofs.BitLengthLemmas

/-- One iteration of the monadic loop, as a standalone `Except`-returning step on the
`MProd` state `⟨a, d⟩` (running approximation `a`, previous shift `d`). This is the loop
body of `isqrtIterative` lifted out: it reads `e = d` (the previous shift), recomputes
`d = c >> s`, and returns the new `⟨a, d⟩`. Each `←` is an operation that could raise. -/
def stepM (c n : ℤ) (r : MProd ℤ ℤ) (s : ℤ) : PyExcept (MProd ℤ ℤ) := do
  let dNew ← pyRshift c s
  let lsh ← pyLshift r.fst (dNew - r.snd - 1)
  let rsh ← pyRshift n (2 * c - r.snd - dNew + 1)
  let q ← pyFloordiv rsh r.fst
  pure ⟨lsh + q, dNew⟩

/-- A `forIn` whose body always yields the result of a monadic step `g` is a `foldlM`
over the same list, specialised to the "always yield" shape the `do` block produces —
this is what lets the proof replace the loop's `forIn` with a `foldlM` it can induct on. -/
theorem forIn_yield_bind_eq_foldlM {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (g : β → α → m β) (L : List α) (init : β) :
    forIn L init (fun a b => g b a >>= fun b' => pure (ForInStep.yield b')) = L.foldlM g init := by
  simp

/-- Indexed invariant rule for a left `foldlM` over `(List.range L).reverse` in `Except`.
Each step must additionally witness that `g x s` takes its `.ok` branch, so the rule
threads `.ok`-ness through the whole fold alongside the invariant.
Reading `motive i x` as "`x` is a valid `.ok` state with `i` iterations still to run",
the seed lands at `i = L`, the result at `i = 0`, and the conclusion packages both the
`.ok`-ness of the whole fold and the final invariant. -/
theorem foldlM_reverseRange_invariant {A : Type} (motive : ℕ → A → Prop)
    (g : A → ℕ → PyExcept A) :
    ∀ (L : ℕ) (init : A), motive L init →
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
theorem stepM_eq_ok {c n : ℤ} (r : MProd ℤ ℤ) (s : ℤ)
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
running `a > 0`, the threaded shift `d = c >> s`, and the near-√ property
`isNearSquareRoot a ⌊n / 4^(c - c>>s)⌋`. -/
theorem monadicLoop_near {c n : ℤ} (hc : 0 ≤ c) (hn : 0 < n)
    (hsc : hasSizeCondition c n) :
    ∃ y : MProd ℤ ℤ, (pyRange (pyBitLength c)).reverse.foldlM (stepM c n) ⟨1, 0⟩ = .ok y
      ∧ 0 < y.fst ∧ isNearSquareRoot y.fst n := by
  -- Bridge the `pyRange` list to `(List.range L).reverse` with ℕ indices.
  have hlist : (pyRange (pyBitLength c)).reverse
      = (List.range (pyBitLength c).toNat).reverse.map Int.ofNat := by
    rw [show pyRange (pyBitLength c) = (List.range (pyBitLength c).toNat).map Int.ofNat from rfl,
        ← List.map_reverse]
  rw [hlist, List.foldlM_map]
  -- `c >> L = 0`, where `L = c.bit_length()`.
  have hz : Int.fdiv c (2 ^ (pyBitLength c).toNat) = 0 := fdiv_two_pow_pyBitLength_eq_zero hc
  set motive : ℕ → MProd ℤ ℤ → Prop := fun (s : ℕ) (r : MProd ℤ ℤ) =>
    0 < r.fst ∧ r.snd = Int.fdiv c (2 ^ s)
      ∧ isNearSquareRoot r.fst (Int.fdiv n (4 ^ (c - Int.fdiv c (2 ^ s)).toNat)) with hmotive
  -- Seed at `s = L`: `c >> L = 0`, base case `isNearSquareRoot 1 ⌊n/4^c⌋`.
  have hseed : motive (pyBitLength c).toNat ⟨1, 0⟩ := by
    refine ⟨one_pos, hz.symm, ?_⟩
    rw [hz]
    obtain ⟨hlo, hhi⟩ := size_condition_at_depth (d := 0) le_rfl hc hsc
    simp only [Int.toNat_zero, pow_zero, zero_add, pow_one] at hlo hhi
    exact ⟨by show (1 - 1) * (1 - 1) < Int.fdiv n (4 ^ (c - 0).toNat); nlinarith [hlo],
           by show Int.fdiv n (4 ^ (c - 0).toNat) < (1 + 1) * (1 + 1); nlinarith [hhi]⟩
  -- Step: one `key_isqrt_lemma` iteration, plus discharging `.ok`-ness of `stepM`.
  have hstep : ∀ s, s < (pyBitLength c).toNat → ∀ x, motive (s + 1) x →
      ∃ y, stepM c n x (Int.ofNat s) = .ok y ∧ motive s y := by
    intro i hi x hx
    simp only [hmotive] at hx ⊢
    set sZ : ℤ := (i : ℤ) with hsZ_def
    have hs_nn : 0 ≤ sZ := by positivity
    have hs_lt : sZ < pyBitLength c := by have := pyBitLength_nonneg c; omega
    have hsi : sZ.toNat = i := Int.toNat_natCast i
    have hsi1 : (sZ + 1).toNat = i + 1 := by omega
    set d_new := Int.fdiv c (2 ^ i) with hd_new_def
    set d_old := Int.fdiv c (2 ^ (i + 1)) with hd_old_def
    set a_old := x.fst with ha_old_def
    obtain ⟨ha_old_pos, hx_snd, hx_near⟩ := hx
    set N_new := Int.fdiv n (4 ^ (c - d_new).toNat) with hN_new_def
    -- align depths with the `Int.fdiv c (2^·)` shape the shift lemmas use
    have hd_new_fdiv : d_new = Int.fdiv c (2 ^ sZ.toNat) := by rw [hsi]
    have hd_old_fdiv : d_old = Int.fdiv c (2 ^ (sZ + 1).toNat) := by rw [hsi1]
    have hd_old_nonneg : 0 ≤ d_old := by rw [hd_old_def]; exact Int.fdiv_nonneg hc (by positivity)
    have hd_new_nonneg : 0 ≤ d_new := by rw [hd_new_def]; exact Int.fdiv_nonneg hc (by positivity)
    have hd_new_le : d_new ≤ c := by
      rw [hd_new_def]; exact Int.fdiv_le_self_of_nonneg hc (by positivity)
    have hK : 0 ≤ d_new - d_old - 1 := by
      rw [hd_new_fdiv]; exact fdiv_two_pow_lshift_nonneg hc hs_nn hs_lt hd_old_fdiv
    have hd_new_pos : 0 < d_new := by omega
    have h_halve : d_old = Int.fdiv d_new 2 := by
      rw [hd_old_fdiv, hd_new_fdiv]; exact fdiv_two_pow_succ c sZ hs_nn
    set k := Int.fdiv (d_new - 1) 2 with hk_def
    have hk_eq : k = d_new - d_old - 1 := by
      rw [hk_def, h_halve,
          Int.fdiv_eq_ediv_of_nonneg (d_new - 1) (by norm_num : (0 : ℤ) ≤ 2),
          Int.fdiv_eq_ediv_of_nonneg d_new (by norm_num : (0 : ℤ) ≤ 2)]
      omega
    have hk_nn : 0 ≤ k := by omega
    set M := (2 : ℤ) ^ k.toNat with hM_def
    have hM_pos : 0 < M := by rw [hM_def]; positivity
    have hsc_new : hasSizeCondition d_new N_new := by
      rw [hN_new_def]; exact size_condition_at_depth hd_new_nonneg hd_new_le hsc
    have hM4 : 4 * M ^ 4 ≤ N_new := by
      have := M_bound_from_size hd_new_pos hsc_new
      rwa [← hk_def, ← hM_def] at this
    have hJ : 0 ≤ 2 * c - d_old - d_new + 1 := by
      have h1 : d_new ≤ c := hd_new_le
      have h2 : d_old ≤ c := by rw [hd_old_fdiv]; exact Int.fdiv_le_self_of_nonneg hc (by positivity)
      omega
    -- the incoming near-√ property at the child depth
    have h_div_bridge :
        Int.fdiv N_new (4 * M ^ 2) = Int.fdiv n (4 ^ (c - d_old).toNat) := by
      rw [hN_new_def, Int.fdiv_fdiv_eq_fdiv_mul n (by positivity) (by positivity)]
      congr 1
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, hM_def]
      simp only [← pow_mul, ← pow_add]
      congr 1
      omega
    have h_near : isNearSquareRoot a_old (Int.fdiv N_new (4 * M ^ 2)) := by
      rw [h_div_bridge]; exact hx_near
    have hX :
        a_old * 2 ^ (d_new - d_old - 1).toNat
            + Int.fdiv (Int.fdiv n (2 ^ (2 * c - d_old - d_new + 1).toNat)) a_old
          = M * a_old + Int.fdiv N_new (4 * M * a_old) := by
      -- The depth-shift glue: rewrite the body's `n`-divisor into the `N_new`-divisor
      -- shape `key_isqrt_body_eq` expects (factoring out `4 ^ (c - d_new)`); the rest
      -- of the algebra is the shared lemma.
      have hbridge : Int.fdiv n (2 ^ (2 * c - d_old - d_new + 1).toNat)
          = Int.fdiv N_new (2 ^ (k + 2).toNat) := by
        rw [hN_new_def, Int.fdiv_fdiv_eq_fdiv_mul n (by positivity) (by positivity)]
        congr 1
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
        simp only [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [show (d_new - d_old - 1).toNat = k.toNat from by rw [hk_eq], hbridge]
      exact key_isqrt_body_eq hk_nn ha_old_pos hM_def
    -- assemble: `stepM` succeeds, and its new `a` is the `key_isqrt_lemma` output
    refine ⟨_, stepM_eq_ok x sZ hs_nn ha_old_pos ?_ ?_, ?_, ?_, ?_⟩
    · rw [hsi, hx_snd]; exact hK
    · rw [hsi, hx_snd]; exact hJ
    · -- positivity of the new `a`
      exact add_pos_of_pos_of_nonneg
        (mul_pos ha_old_pos (by positivity))
        (Int.fdiv_nonneg (Int.fdiv_nonneg hn.le (by positivity)) ha_old_pos.le)
    · -- new `d = c >> i`
      rfl
    · -- near-√ at the new depth: the body's new `a` is the `key_isqrt_lemma` output
      rw [hx_snd]
      show isNearSquareRoot (a_old * 2 ^ (d_new - d_old - 1).toNat
          + Int.fdiv (Int.fdiv n (2 ^ (2 * c - d_old - d_new + 1).toNat)) a_old) N_new
      rw [hX]
      exact key_isqrt_lemma hM_pos ha_old_pos hM4 h_near
  obtain ⟨y, hy_eq, hy_pos, _hy_d, hy_near⟩ :=
    foldlM_reverseRange_invariant motive (fun x s => stepM c n x (Int.ofNat s))
      (pyBitLength c).toNat ⟨1, 0⟩ hseed hstep
  -- Result at `s = 0`: `c >> 0 = c`, divisor `4^(c-c) = 1`, so a near-√ of `n`.
  refine ⟨y, hy_eq, hy_pos, ?_⟩
  simpa [Int.fdiv_one, Int.sub_self] using hy_near

/-- Correctness of the monadic integer square root `isqrtIterative`.

For `n < 0` it raises exactly the `ValueError` CPython does; otherwise it returns `.ok v`
with `v = ⌊√n⌋` (`isIntegerSquareRoot v n`). The proof reduces the `do`-block to the
`foldlM` characterised by `monadicLoop_near` — establishing en route that none of the
`Except` operations ever take their error branch for `n ≥ 0` — and closes the `n ≥ 1`
case with the same final `a-1`/`a` adjustment (`isNearSquareRoot.toIntegerSquareRoot`) as
the recursive and iterative proofs. -/
theorem isCorrectIsqrt_isqrtIterative : isCorrectIsqrt isqrtIterative := by
  refine ⟨?_, ?_⟩
  · -- Nonnegative `n`: the loop runs, never raises, and returns `⌊√n⌋`.
    intro n hn
    show ∃ h : Isqrt.succeeds (isqrtIterative n),
      isIntegerSquareRoot (Isqrt.returnValue (isqrtIterative n) h) n
    rcases eq_or_lt_of_le hn with rfl | hpos
    · -- n = 0: special-cased to 0.
      refine returnValue_satisfies (by unfold isqrtIterative; norm_num; rfl)
        (fun a => isIntegerSquareRoot a 0) ?_
      show isIntegerSquareRoot 0 0; unfold isIntegerSquareRoot; norm_num
    · -- 0 < n: the loop runs and never raises.
      have hn0 : n ≠ 0 := ne_of_gt hpos
      obtain ⟨y, hy_eq, _hy_pos, hy_near⟩ :=
        monadicLoop_near (c := (pyBitLength n - 1).fdiv 2) (isqrt_c_nonneg hn0) hpos
          (size_condition_initial hpos)
      have hred : isqrtIterative n = .ok (y.fst - if y.fst * y.fst > n then 1 else 0) := by
        conv_lhs => unfold isqrtIterative
        simp only [if_neg (show ¬ n < 0 by omega), if_neg hn0, pure_bind,
          pyFloordiv_eq_ok (show (2 : ℤ) ≠ 0 by norm_num)]
        rw [show (Except.ok ((pyBitLength n - 1).fdiv 2) : PyExcept ℤ)
              = pure ((pyBitLength n - 1).fdiv 2) from rfl, pure_bind]
        have key := forIn_yield_bind_eq_foldlM (stepM ((pyBitLength n - 1).fdiv 2) n)
          (pyRange (pyBitLength ((pyBitLength n - 1).fdiv 2))).reverse ⟨1, 0⟩
        conv at key => lhs; simp only [stepM, bind_assoc, pure_bind]
        rw [key, hy_eq]; rfl
      have hp : isIntegerSquareRoot (y.fst - if y.fst * y.fst > n then 1 else 0) n := by
        have hadj : (y.fst - if y.fst * y.fst > n then 1 else 0)
            = (if n < y.fst * y.fst then y.fst - 1 else y.fst) := by split <;> simp
        rw [hadj]
        exact hy_near.toIntegerSquareRoot
      exact returnValue_satisfies hred (fun a => isIntegerSquareRoot a n) hp
  · -- Negative `n`: the first guard raises, short-circuiting the `do` block.
    intro n hn
    show ∃ h : Isqrt.fails (isqrtIterative n),
      Isqrt.exceptionRaised (isqrtIterative n) h = .valueError "isqrt() argument must be nonnegative"
    have herr : isqrtIterative n
        = .error (.valueError "isqrt() argument must be nonnegative") := by
      unfold isqrtIterative; rw [if_pos hn]; rfl
    exact exceptionRaised_satisfies herr
      (fun e => e = .valueError "isqrt() argument must be nonnegative") rfl
