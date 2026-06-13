/-
Correctness of the iterative integer square root `isqrtIterative` (`for … in` form).

Strategy: reuse the recursive proof's algebra unchanged. As in every translation of this
loop, one iteration is exactly one `key_isqrt_lemma` step; only the harness around that
step differs. Here the loop is Lean's `for h : s in (List.range L).reverse do …` in the
`Id` monad, so the proof has two layers:

1. **Reduce the loop to a fold.** Lean desugars `for h : s in xs do … (mut a)` into
   `forIn' xs a (fun s h a => … .yield …)`; the library lemma
   `List.forIn'_pure_yield_eq_foldl` rewrites that (in `Id`) to a `List.foldl` over
   `xs.attach`. The membership proof `h : s ∈ xs` that `forIn'` threads is then dropped:
   on every list element the bound `s < L` holds, so the body agrees with an index-guarded
   total step, and `List.foldl_attach` discards the `.attach`. What remains is a plain
   `List.foldl` over `(List.range L).reverse`.

2. **Run the position-indexed invariant.** `foldl_reverseRange_invariant` is a
   loop-invariant rule for a left fold over a reversed range: since `(List.range L).reverse`
   is `[L-1, …, 1, 0]`, folding it left visits the loop indices in descending order, and the
   loop property is *indexed by the position* `s` (the loop counter):

       motive s a := isNearSquareRoot a ⌊n / 4^(c - c>>s)⌋

   The seed lands at `s = L` (where `c >> L = 0`) and the result at `s = 0` (where
   `c >> 0 = c`, collapsing `4^(c-d)` to `4^0 = 1`). The per-iteration body is one
   `key_isqrt_lemma` step, identical to the one in the recursive proof.

`iterStep` is the loop body as a standalone function (the `for`-loop's `a := …` line); the
correctness file owns it because `Iterative.lean` inlines the body to read line-for-line
with the Python.

Gotcha when writing the motive: `py>>` is `infixl:60` and `-` is `infixl:65`, so
`c - c py>> s` parses as `(c - c) py>> s`. Parenthesize: `4^(c - (c py>> s))`.

The main result is `isIntegerSquareRoot_isqrtIterative`, the same statement as `isIntegerSquareRoot_isqrt`.
-/

import Isqrt.Iterative
import Isqrt.KeyLemma
import Isqrt.SizeConditions

/-! ## A reversed-range `foldl` invariant rule -/

/-- Indexed invariant rule for a left fold over `(List.range L).reverse` — the standard
loop-invariant principle, specialised to a descending reversed range. Since the list is `[L-1, …, 1, 0]`,
`foldl g init` applies `g · (L-1)`, …, `g · 0` in turn, so reading `motive i x` as "`x`
is a valid state with `i` iterations still to run" gives `i = L` at the seed, `i = 0` at
the result, and each step the index bound `s < L` for free. Proved by induction on `L`
via `List.range_succ` (no dependent `.attach` rewriting — the body `g` is plain). -/
theorem foldl_reverseRange_invariant {A : Type _} (motive : Nat → A → Prop)
    (g : A → Nat → A) :
    ∀ (L : Nat) (init : A), motive L init →
      (∀ s, s < L → ∀ x, motive (s + 1) x → motive s (g x s)) →
      motive 0 ((List.range L).reverse.foldl g init) := by
  intro L
  induction L with
  | zero => intro init hinit _; simpa using hinit
  | succ L ih =>
    intro init hinit hstep
    have hcons : (List.range (L + 1)).reverse = L :: (List.range L).reverse := by
      rw [List.range_succ, List.reverse_append]; rfl
    rw [hcons, List.foldl_cons]
    apply ih (g init L)
    · exact hstep L (Nat.lt_succ_self L) init hinit
    · intro s hs x hmot; exact hstep s (Nat.lt_succ_of_lt hs) x hmot

/-! ## The loop body, as a standalone function -/

/-- One iteration of the reversed-range loop, at index `s`: the `for`-loop's `a := …`
line lifted out as a function. Reads line-for-line with the Python suite

    e = c >> (s + 1); d = c >> s; a = (a << d-e-1) + (n >> (2c-d-e+1)) // a

`s` is the loop variable (a `ℕ`, arriving with its bound `s < L`), and the running `a > 0`
is the subtype state. The shift-nonneg facts `hK`, `hJ` (and `ha_pos`) are in scope, so
the py-ops' default `by omega` discharges their preconditions; positivity of the new `a`
re-establishes the subtype invariant. This is the same body `Iterative.lean` inlines into
the `do` block; it lives here because that translation keeps the body inline for fidelity
to the Python. -/
def iterStep (c n : ℤ) (hc : 0 ≤ c) (hn : 0 ≤ n)
    (s : ℕ) (_hs : s < (pyBitLength c).toNat) (a : {a : ℤ // 0 < a}) :
    {a : ℤ // 0 < a} :=
  let av := a.val
  have ha_pos : 0 < av := a.property
  -- the loop variable as an integer, with its bounds
  let sZ : ℤ := s
  have hs_nn : 0 ≤ sZ := by positivity
  have hs_lt : sZ < pyBitLength c := by
    have hbl := pyBitLength_nonneg c; omega
  -- one pass of the loop body, line for line with the Python:
  --   e = c >> (s + 1); d = c >> s; a = (a << d-e-1) + (n >> (2*c-d-e+1)) // a
  let e := c py>> (sZ + 1)
  let d := c py>> sZ
  have hd_eq : e = c py>> (sZ + 1)  := rfl
  have hK : 0 ≤ d - e - 1         := iter_lshift_nonneg hc hs_nn hs_lt hd_eq
  have hJ : 0 ≤ 2 * c - d - e + 1 := iter_rshift_nonneg hc hs_nn hd_eq
  ⟨(av py<< (d - e - 1)) + (n py>> (2 * c - d - e + 1)) py// av,
   pyLshift_add_pyFloordiv_pos ha_pos hn hK hJ⟩

/-- `iterStep`'s new `a`, with the py-ops unfolded to `Int.fdiv`/`2^…` form — the shape
`key_isqrt_lemma` consumes. -/
theorem iterStep_val (c n : ℤ) (hc : 0 ≤ c) (hn : 0 ≤ n) (s : ℕ)
    (hs : s < (pyBitLength c).toNat) (a : {a : ℤ // 0 < a}) :
    (iterStep c n hc hn s hs a).val =
      a.val * 2 ^ ((c py>> (s : ℤ)) - (c py>> ((s : ℤ) + 1)) - 1).toNat
      + Int.fdiv (Int.fdiv n
          (2 ^ (2 * c - (c py>> (s : ℤ)) - (c py>> ((s : ℤ) + 1)) + 1).toNat)) a.val := by
  simp only [iterStep, pyLshift_def, pyRshift_def, pyFloordiv_def]

/-! ## Near-square-root of the loop result -/

/-- The `for`-loop result is a near square root of `n`. The loop reduces to a
`List.foldl` over `(List.range L).reverse` (see the module note), and
`foldl_reverseRange_invariant` runs the position-indexed loop property
`motive s a := isNearSquareRoot a ⌊n/4^(c - c>>s)⌋`: the seed (`s = L`, `c>>L = 0`) is
`isNearSquareRoot 1 ⌊n/4^c⌋` (base case), each step is one `key_isqrt_lemma`, and at the result
(`s = 0`) `c>>0 = c` collapses the divisor to `4^0 = 1`.

The fold body is stated via `iterStep` applied at each element's index (with the bound
read off the `.attach` membership proof), matching the loop `Iterative.lean` produces. -/
theorem loopFold_near {c n : ℤ} (hc : 0 ≤ c) (hn : 0 < n)
    (hsc : hasSizeCondition c n) :
    isNearSquareRoot ((List.range (pyBitLength c).toNat).reverse.attach.foldl
      (fun (b : {a : ℤ // 0 < a})
          (x : {s // s ∈ (List.range (pyBitLength c).toNat).reverse}) =>
        iterStep c n hc hn.le x.1 (List.mem_range.mp (List.mem_reverse.mp x.2)) b)
      ⟨1, one_pos⟩).val n := by
  -- Drop the membership proof: the attach-fold equals a plain fold of the index-guarded
  -- body (the guard `s < L` is satisfied by every list element), via `List.foldl_attach`.
  rw [show (List.range (pyBitLength c).toNat).reverse.attach.foldl
        (fun (b : {a : ℤ // 0 < a})
            (x : {s // s ∈ (List.range (pyBitLength c).toNat).reverse}) =>
          iterStep c n hc hn.le x.1 (List.mem_range.mp (List.mem_reverse.mp x.2)) b)
        ⟨1, one_pos⟩
      = (List.range (pyBitLength c).toNat).reverse.foldl
          (fun (b : {a : ℤ // 0 < a}) s =>
            if h : s < (pyBitLength c).toNat then iterStep c n hc hn.le s h b else b)
          ⟨1, one_pos⟩ from by
        conv_rhs => rw [← List.foldl_attach]
        congr 1
        funext b x
        rw [dif_pos (List.mem_range.mp (List.mem_reverse.mp x.2))]]
  -- The indexed loop property at the result (`s = 0`) collapses to `isNearSquareRoot _ n`.
  suffices h : isNearSquareRoot
      ((List.range (pyBitLength c).toNat).reverse.foldl
        (fun (b : {a : ℤ // 0 < a}) s =>
          if h : s < (pyBitLength c).toNat then iterStep c n hc hn.le s h b else b)
        ⟨1, one_pos⟩).val
      (Int.fdiv n (4 ^ (c - (c py>> ((0 : ℕ) : ℤ))).toNat)) by
    simpa [pyRshift_def, Int.fdiv_one] using h
  refine foldl_reverseRange_invariant
    (motive := fun (s : ℕ) (a : {a : ℤ // 0 < a}) =>
      isNearSquareRoot a.val (Int.fdiv n (4 ^ (c - (c py>> (↑s : ℤ))).toNat)))
    (fun (b : {a : ℤ // 0 < a}) s =>
      if h : s < (pyBitLength c).toNat then iterStep c n hc hn.le s h b else b)
    (pyBitLength c).toNat ⟨1, one_pos⟩ ?hinit ?hstep
  case hinit =>
    -- Seed: at `s = L`, `c >> L = 0`, so `isNearSquareRoot 1 ⌊n/4^(c-0)⌋` (base case).
    show isNearSquareRoot (1 : ℤ) (Int.fdiv n (4 ^ (c - (c py>> (↑(pyBitLength c).toNat : ℤ))).toNat))
    have hz : c py>> (↑(pyBitLength c).toNat : ℤ) = 0 := by
      rw [pyRshift_def]
      have h := pyRshift_pyBitLength_eq_zero hc
      rw [pyRshift_def] at h
      rwa [Int.toNat_natCast]
    simp only [hz]
    obtain ⟨hlo, hhi⟩ := size_condition_at_depth (d := 0) le_rfl hc hsc
    simp only [Int.toNat_zero, pow_zero, zero_add, pow_one] at hlo hhi
    refine ⟨?_, ?_⟩
    · show (1 - 1) * (1 - 1) < Int.fdiv n (4 ^ (c - 0).toNat); nlinarith [hlo]
    · show Int.fdiv n (4 ^ (c - 0).toNat) < (1 + 1) * (1 + 1); nlinarith [hhi]
  case hstep =>
    -- One iteration = one `key_isqrt_lemma` step at parent depth `d_new = c >> s`.
    intro i hi x hx
    -- discharge the index guard (`i < L`), exposing `iterStep`
    simp only [dif_pos hi]
    rw [iterStep_val c n hc hn.le i hi x]
    -- unfold the py-ops to `Int.fdiv`/`2^…` form everywhere (drops the proof args),
    -- then align the incoming property's cast `↑(i+1)` with `↑i + 1`
    simp only [pyRshift_def] at hx ⊢
    rw [show (↑(i + 1) : ℤ) = (↑i : ℤ) + 1 by push_cast; ring] at hx
    set s := (i : ℤ) with hs_def
    have hs_nn : 0 ≤ s := by positivity
    have hs_lt : s < pyBitLength c := by
      have hbl := pyBitLength_nonneg c; omega
    set d_new := Int.fdiv c (2 ^ s.toNat) with hd_new_def
    set d_old := Int.fdiv c (2 ^ (s + 1).toNat) with hd_old_def
    set a_old := x.val with ha_old_def
    have ha_old_pos : 0 < a_old := x.property
    set N_new := Int.fdiv n (4 ^ (c - d_new).toNat) with hN_new_def
    -- bridge back to py>> form for the shift lemmas (defeq via `pyRshift_def`)
    have hd_new_py : d_new = c py>> s := by rw [pyRshift_def]
    have hd_old_eq : d_old = c py>> (s + 1) := by rw [pyRshift_def]
    -- positivity / ordering of the depths
    have hd_old_nonneg : 0 ≤ d_old := by rw [hd_old_eq]; exact pyRshift_nonneg hc
    have hd_new_nonneg : 0 ≤ d_new := by
      rw [hd_new_def]; exact Int.fdiv_nonneg hc (by positivity)
    have hd_new_le : d_new ≤ c := by
      rw [hd_new_def]; exact Int.fdiv_le_self_of_nonneg hc (by positivity)
    -- left-shift amount nonneg, hence d_new ≥ 1
    have hK : 0 ≤ d_new - d_old - 1 := by
      rw [hd_new_py]; exact iter_lshift_nonneg hc hs_nn hs_lt hd_old_eq
    have hd_new_pos : 0 < d_new := by omega
    -- d_old = d_new / 2 (the halving link)
    have h_halve : d_old = Int.fdiv d_new 2 := by
      rw [hd_old_eq, hd_new_def]; exact pyRshift_succ c s hs_nn
    -- k and M = 2^k
    set k := (d_new - 1) py// 2 with hk_def
    have hk_eq : k = d_new - d_old - 1 := by
      rw [hk_def]; simp only [pyFloordiv_def]; rw [h_halve,
          Int.fdiv_eq_ediv_of_nonneg (d_new - 1) (by norm_num : (0 : ℤ) ≤ 2),
          Int.fdiv_eq_ediv_of_nonneg d_new (by norm_num : (0 : ℤ) ≤ 2)]
      omega
    set M := (2 : ℤ) ^ k.toNat with hM_def
    have hM_pos : 0 < M := by rw [hM_def]; positivity
    -- 4·M⁴ ≤ N_new, from the size condition at depth d_new
    have hsc_new : hasSizeCondition d_new N_new := by
      rw [hN_new_def]; exact size_condition_at_depth hd_new_nonneg hd_new_le hsc
    have hM4 : 4 * M ^ 4 ≤ N_new := by
      have := M_bound_from_size hd_new_pos hsc_new
      rwa [← hk_def, ← hM_def] at this
    -- near-√ at the child: isNearSquareRoot a_old ⌊N_new/4M²⌋ = the incoming property `hx`
    have h_div_bridge :
        Int.fdiv N_new (4 * M ^ 2) = Int.fdiv n (4 ^ (c - d_old).toNat) := by
      rw [hN_new_def, Int.fdiv_fdiv_eq_fdiv_mul n (by positivity) (by positivity)]
      congr 1
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, hM_def]
      simp only [← pow_mul, ← pow_add]
      congr 1
      omega
    have h_near : isNearSquareRoot a_old (Int.fdiv N_new (4 * M ^ 2)) := by
      rw [h_div_bridge]; exact hx
    -- the body's new `a` is exactly the `key_isqrt_lemma` output
    have hMa_nn : (0 : ℤ) ≤ 4 * M * a_old :=
      mul_nonneg (mul_nonneg (by norm_num) hM_pos.le) ha_old_pos.le
    have hX :
        a_old * 2 ^ (d_new - d_old - 1).toNat
            + Int.fdiv (Int.fdiv n (2 ^ (2 * c - d_new - d_old + 1).toNat)) a_old
          = M * a_old + Int.fdiv N_new (4 * M * a_old) := by
      congr 1
      · rw [hM_def, show (d_new - d_old - 1).toNat = k.toNat from by rw [hk_eq]]
        ring
      · rw [hN_new_def,
            Int.fdiv_fdiv_eq_fdiv_mul n (by positivity) ha_old_pos.le,
            Int.fdiv_fdiv_eq_fdiv_mul n (by positivity) hMa_nn]
        congr 1
        have hpow_a : (2 : ℤ) ^ (2 * c - d_new - d_old + 1).toNat
                        = 4 ^ (c - d_new).toNat * (4 * M) := by
          rw [hM_def, show (4 : ℤ) = 2 ^ 2 by norm_num]
          simp only [← pow_mul, ← pow_add]
          congr 1
          omega
        rw [hpow_a]; ring
    rw [hX]
    exact key_isqrt_lemma hM_pos ha_old_pos hM4 h_near

/-! ## Correctness of `isqrtIterative` -/

/-- Main correctness theorem for the iterative form: `isqrtIterative n` is the floor of
`√n`. Same statement as `isIntegerSquareRoot_isqrt`.

For `n ≠ 0`, unfolding the `do` block and applying `List.forIn'_pure_yield_eq_foldl`
turns the `for`-loop into the `List.foldl` that `loopFold_near` characterises; the result
is a near square root, and the final `a - 1`/`a` adjustment (`isNearSquareRoot.toIntegerSquareRoot`)
pins it to `⌊√n⌋`. -/
theorem isIntegerSquareRoot_isqrtIterative (n : ℤ) (hn : 0 ≤ n) :
    isIntegerSquareRoot (isqrtIterative n hn) n := by
  by_cases hn0 : n = 0
  · subst hn0; simp [isqrtIterative, isIntegerSquareRoot]
  · have hn_pos : 0 < n := lt_of_le_of_ne hn (Ne.symm hn0)
    have hc : 0 ≤ (pyBitLength n - 1) py// 2 := isqrt_c_nonneg hn0
    have h_near := loopFold_near (c := (pyBitLength n - 1) py// 2) hc hn_pos
      (size_condition_initial hn_pos)
    unfold isqrtIterative
    simp only [hn0, ↓reduceDIte, pure_bind, List.forIn'_pure_yield_eq_foldl, Id.run_pure]
    exact h_near.toIntegerSquareRoot
