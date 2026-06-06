/-
The iterative integer square root, matching `isqrt_iterative.py`:

    def isqrt(n):
        c = (n.bit_length() - 1) // 2
        s = c.bit_length()
        d = 0
        a = 1
        while s > 0:
            e = d
            s = s - 1
            d = c >> s
            a = (a << d-e-1) + (n >> 2*c-d-e+1) // a
        return a if a*a <= n else a - 1

This is `isqrt_aux` unrolled bottom-up: the loop's `d` climbs the chain
`c >> j` that the recursion descends, and each iteration is one recursive step.
The translation uses the generic `pyWhile` combinator (`Isqrt.While`). The
persistent loop state `(s, d, a)` lives in a subtype carrying the minimal
well-definedness invariant `iterInv`; `e` is loop-local (the incoming `d`).

This module holds the definition `isqrtIterative` and the named lemmas its body
needs to typecheck (the py-op precondition proofs — kept out of the `pyWhile`
call per the ADR 0001 elaboration-order gotcha). Correctness lives in
`Isqrt.IterativeCorrectness`. See `PLAN.md` (Iterative variant) and
`CONTEXT.md`.
-/

import Isqrt.Algorithm
import Isqrt.While

/-! ## Loop state and its well-definedness invariant -/

/-- Persistent loop state of the iterative isqrt: the Python locals `s, d, a`
that survive across iterations (`e` is loop-local). -/
structure IterState where
  s : ℤ
  d : ℤ
  a : ℤ

/-- The well-definedness invariant bundled into the loop-state subtype: the
minimal facts the body needs to discharge its py-op preconditions, plus the
variant's nonnegativity. `c` is the fixed recursion bound (closure-captured).
The near-√ property and the size condition are deliberately *not* here. -/
def iterInv (c : ℤ) (st : IterState) : Prop :=
  0 ≤ st.s ∧ st.s ≤ pyBitLength c ∧ st.d = Int.fdiv c (2 ^ st.s.toNat) ∧ 0 < st.a

/-- The loop-state type handed to `pyWhile`: states carrying `iterInv c`. -/
abbrev IterSigma (c : ℤ) := { st : IterState // iterInv c st }

/-! ## Arithmetic helper -/

/-- Floor-dividing a nonneg integer by a positive integer cannot increase it. -/
private theorem fdiv_le_self_of_nonneg {c m : ℤ} (hc : 0 ≤ c) (hm : 0 < m) :
    c.fdiv m ≤ c := by
  have h0 : 0 ≤ c.fdiv m := Int.fdiv_nonneg hc hm.le
  have h1 : c.fdiv m * m ≤ c := Int.fdiv_mul_le_self hm
  nlinarith [h1, mul_nonneg h0 (show (0 : ℤ) ≤ m - 1 by omega)]

/-! ## Seed -/

/-- At the seed `s = c.bit_length()`, the shift `c >> s` is `0` (since
`c < 2^(c.bit_length())`). This makes the seed satisfy `iterInv`. -/
theorem seed_d_eq {c : ℤ} (hc : 0 ≤ c) :
    Int.fdiv c (2 ^ (pyBitLength c).toNat) = 0 := by
  rw [Int.fdiv_eq_ediv_of_nonneg c (by positivity)]
  apply Int.ediv_eq_zero_of_lt hc
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc
  have hbl : (pyBitLength (↑cn : ℤ)).toNat = natBitLength cn := by
    rw [show pyBitLength (↑cn : ℤ) = ↑(natBitLength cn) from by
          simp [pyBitLength]]
    exact Int.toNat_natCast _
  rw [hbl]
  exact_mod_cast lt_two_pow_natBitLength cn

/-! ## Body precondition lemmas (named, per ADR 0001 gotcha) -/

/-- The left-shift amount `d' - d - 1` is nonneg, where `d' = c >> (s-1)` and
`d = c >> s` for `0 < s ≤ c.bit_length()`. The body's hardest precondition: it
needs `d' ≥ 1` (from `s ≤ L`, via `2^(L-1) ≤ c`) and `d = d' // 2`. -/
theorem iter_lshift_nonneg {c s d : ℤ} (hc : 0 ≤ c) (hs_pos : 0 < s)
    (hs_le : s ≤ pyBitLength c) (hd : d = Int.fdiv c (2 ^ s.toNat)) :
    0 ≤ Int.fdiv c (2 ^ (s - 1).toNat) - d - 1 := by
  set d' := Int.fdiv c (2 ^ (s - 1).toNat) with hd'
  have hsuc : s.toNat = (s - 1).toNat + 1 := by omega
  -- d = d' // 2
  have hd2 : d = Int.fdiv d' 2 := by
    rw [hd, hsuc, pow_succ,
        ← Int.fdiv_fdiv_eq_fdiv_mul c (by positivity) (by norm_num), ← hd']
  -- d' ≥ 1, from 2^(s-1).toNat ≤ c
  have hd'_ge1 : 1 ≤ d' := by
    rw [hd', Int.le_fdiv_iff_mul_le (by positivity), one_mul]
    obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc
    rw [show pyBitLength (↑cn : ℤ) = ↑(natBitLength cn) from by
          simp [pyBitLength]] at hs_le
    have hbl_pos : 0 < natBitLength cn := by omega
    have hcn_pos : 0 < cn := natBitLength_pos_iff.mp hbl_pos
    have hbound : 2 ^ (natBitLength cn - 1) ≤ cn := two_pow_pred_natBitLength_le hcn_pos
    have hexp : (s - 1).toNat ≤ natBitLength cn - 1 := by omega
    calc (2 : ℤ) ^ (s - 1).toNat
        ≤ (2 : ℤ) ^ (natBitLength cn - 1) := by
          apply pow_le_pow_right₀ (by norm_num) hexp
      _ = ((2 ^ (natBitLength cn - 1) : ℕ) : ℤ) := by push_cast; rfl
      _ ≤ (↑cn : ℤ) := by exact_mod_cast hbound
  rw [hd2, Int.fdiv_eq_ediv_of_nonneg d' (by norm_num : (0 : ℤ) ≤ 2)]
  omega

/-- The right-shift amount `2c - d' - d + 1` is nonneg, where `d' = c >> (s-1)`
and `d = c >> s`. Both shifts are `≤ c` (for `0 ≤ c`), so the amount is `≥ 1`. -/
theorem iter_rshift_nonneg {c s d : ℤ} (hc : 0 ≤ c)
    (hd : d = Int.fdiv c (2 ^ s.toNat)) :
    0 ≤ 2 * c - Int.fdiv c (2 ^ (s - 1).toNat) - d + 1 := by
  have h1 : Int.fdiv c (2 ^ (s - 1).toNat) ≤ c := fdiv_le_self_of_nonneg hc (by positivity)
  have h2 : Int.fdiv c (2 ^ s.toNat) ≤ c := fdiv_le_self_of_nonneg hc (by positivity)
  rw [hd]; omega

/-- The body's new `a` is positive (parallels `isqrt_aux_return_pos`, but with
independent shift amounts `K`, `J`). Used to re-establish `iterInv`. -/
theorem isqrtIterative_body_pos {a n K J : ℤ}
    (ha : 0 < a) (hn : 0 ≤ n) (hK : 0 ≤ K) (hJ : 0 ≤ J) :
    0 < (a py<< K) + (n py>> J) py// a := by
  simp only [pyLshift_def, pyFloordiv_def, pyRshift_def]
  have h_shift_pos : 0 < a * 2 ^ K.toNat := Int.mul_pos ha (by positivity)
  have h_div_nonneg : 0 ≤ (n.fdiv (2 ^ J.toNat)).fdiv a :=
    Int.fdiv_nonneg (Int.fdiv_nonneg hn (by positivity)) ha.le
  omega

/-! ## The loop body -/

/-- One execution of the loop body. Mirrors the Python suite

    e = d; s = s - 1; d = c >> s; a = (a << d-e-1) + (n >> 2c-d-e+1) // a

(`e` is the incoming `d`, i.e. `st.val.d`). The shift-nonneg preconditions are
discharged by the named lemmas above, and `iterInv` is re-established for the
new state. Defined as a standalone `def` (not inline in the `pyWhile` call) so
the precondition proofs don't entangle with the measure-decrease goal. -/
def iterBody (c n : ℤ) (hc : 0 ≤ c) (hn : 0 ≤ n)
    (st : IterSigma c) (h : 0 < st.val.s) : IterSigma c :=
  have hs'_nn : 0 ≤ st.val.s - 1 := by omega
  have hd_eq : st.val.d = Int.fdiv c (2 ^ st.val.s.toNat) := st.property.2.2.1
  have hs_le : st.val.s ≤ pyBitLength c := st.property.2.1
  have ha_pos : 0 < st.val.a := st.property.2.2.2
  let d' : ℤ := c py>> (st.val.s - 1)
  have hK : 0 ≤ d' - st.val.d - 1 := iter_lshift_nonneg hc h hs_le hd_eq
  have hJ : 0 ≤ 2 * c - d' - st.val.d + 1 := iter_rshift_nonneg hc hd_eq
  -- `hK`, `hJ`, `ha_pos` are in scope, so the py-ops' default `by omega`
  -- discharges the shift-nonneg / nonzero-divisor preconditions.
  ⟨{ s := st.val.s - 1
     d := d'
     a := (st.val.a py<< (d' - st.val.d - 1))
            + (n py>> (2 * c - d' - st.val.d + 1)) py// st.val.a },
   ⟨hs'_nn, by show st.val.s - 1 ≤ pyBitLength c; omega, rfl,
    isqrtIterative_body_pos ha_pos hn hK hJ⟩⟩

/-- The body decrements `s`. (Drives the measure-decrease proof.) -/
@[simp] theorem iterBody_s {c n : ℤ} {hc : 0 ≤ c} {hn : 0 ≤ n}
    {st : IterSigma c} {h : 0 < st.val.s} :
    (iterBody c n hc hn st h).val.s = st.val.s - 1 := rfl

/-- The body sets `d` to `c >> (s-1)`. -/
@[simp] theorem iterBody_d {c n : ℤ} {hc : 0 ≤ c} {hn : 0 ≤ n}
    {st : IterSigma c} {h : 0 < st.val.s} :
    (iterBody c n hc hn st h).val.d = Int.fdiv c (2 ^ (st.val.s - 1).toNat) := rfl

/-! ## The iterative isqrt -/

/-- Integer square root, iterative form (`isqrt_iterative.py`).

Precondition `0 ≤ n`. `n = 0` is special-cased to `0` (the loop would otherwise
shift by a negative amount), mirroring the recursive `isqrt`. For `n ≥ 1` the
`while s > 0` loop is the faithful `pyWhile` translation; the final line returns
`a` or `a - 1` exactly as the Python `return a if a*a <= n else a - 1`. -/
def isqrtIterative (n : ℤ) (n_nonneg : 0 ≤ n := by omega) : ℤ :=
  if _ : n = 0 then 0
  else
    let c := (pyBitLength n - 1) py// 2
    have hc : 0 ≤ c := isqrt_c_nonneg (by omega)
    let seed : IterSigma c :=
      ⟨{ s := pyBitLength c, d := 0, a := 1 },
       ⟨pyBitLength_nonneg c, le_refl _, (seed_d_eq hc).symm, one_pos⟩⟩
    let result := pyWhile seed (fun st => 0 < st.val.s) (iterBody c n hc n_nonneg)
                    (fun st => st.val.s.toNat)
                    (fun st h => by simp_wf; omega)
    let a := result.val.val.a
    if a * a ≤ n then a else a - 1
