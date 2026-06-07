/-
Python's `math.integer` module defines an `isqrt` function that computes the integer
part of the square root of a nonnegative integer input. The implementation of
`math.integer.isqrt` is in C, but the comments in the C source include equivalent
Python code, reproduced verbatim here for easy reference.

    def isqrt(n):
        """
        Return the integer part of the square root of the input.
        """
        n = operator.index(n)

        if n < 0:
            raise ValueError("isqrt() argument must be nonnegative")
        if n == 0:
            return 0

        c = (n.bit_length() - 1) // 2
        a = 1
        d = 0
        for s in reversed(range(c.bit_length())):
            # Loop invariant: (a-1)**2 < (n >> 2*(c - d)) < (a+1)**2
            e = d
            d = c >> s
            a = (a << d - e - 1) + (n >> 2*c - e - d + 1) // a

        return a - (a*a > n)

xref: https://github.com/python/cpython/blob/ab930175e7e909aaa3ec7e761bfdbb886677bebb/Modules/mathintegermodule.c#L189-L211
xref: https://github.com/python/cpython/blob/73934b9da07daefb203e7d26089e7486a1ce4fdf/Modules/mathmodule.c#L1513-L1535

Here's a minor rewrite of the same code that makes it slightly more amenable to direct
translation into Lean (while also making it slightly less idiomatic from a Python
point of view). Key changes:

- Drop the `index` translation and negative `n` guard; assume that the
  input is a nonnegative `int`. Behaviour for negative n is considered undefined.
- Add type hints.
- Replace the `for` loop with an equivalent `while` loop.
- Remove the implicit bool-to-int conversion in the final return.
- Place the main body in an else branch.


    def isqrt(n: int) -> int:
        """For nonnegative n, find a satisfying a * a <= n < (a + 1) * (a + 1)."""
        if n == 0:
            return 0
        else:
            c = (n.bit_length() - 1) // 2

            a = 1
            d = 0
            s = c.bit_length() - 1
            while s >= 0:
                e = d
                d = c >> s
                a = (a << d - e - 1) + (n >> (2 * c - d - e + 1)) // a
                s = s - 1

            return a - 1 if a * a > n else a


This rewritten version is our target for translation into Lean.

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
minimal facts the body needs to discharge its py-op preconditions. `c` is the
fixed recursion bound (closure-captured). With the loop variable `s` running
`c.bit_length() - 1` down to `-1`, the persistent `d` holds `c >> (s + 1)` — the
shift from the *previous* iteration. The variant's nonnegativity is supplied by
the loop condition (`0 ≤ s`), so it is not bundled here; nor are the near-√
property and the size condition. -/
def iterInv (c : ℤ) (st : IterState) : Prop :=
  st.s < pyBitLength c ∧ st.d = Int.fdiv c (2 ^ (st.s + 1).toNat) ∧ 0 < st.a

/-- The loop-state type handed to `pyWhile`: states carrying `iterInv c`. -/
abbrev IterSigma (c : ℤ) := { st : IterState // iterInv c st }

/-! ## Arithmetic helper -/

/-- Floor-dividing a nonneg integer by a positive integer cannot increase it. -/
theorem fdiv_le_self_of_nonneg {c m : ℤ} (hc : 0 ≤ c) (hm : 0 < m) :
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

/-- The depth halves each iteration: `c >> (s+1) = (c >> s) // 2` for `0 ≤ s`.
This is the body's `e = d // 2` link (the recursion's `c ↦ c // 2`). Shared by
`iter_lshift_nonneg` and the correctness proof's preservation step. (No sign
hypothesis on `c` is needed — only the divisors must be nonneg.) -/
theorem iter_d_halving {c s : ℤ} (hs_nn : 0 ≤ s) :
    Int.fdiv c (2 ^ (s + 1).toNat) = Int.fdiv (Int.fdiv c (2 ^ s.toNat)) 2 := by
  have hsuc : (s + 1).toNat = s.toNat + 1 := by omega
  rw [hsuc, pow_succ, ← Int.fdiv_fdiv_eq_fdiv_mul c (by positivity) (by norm_num)]

/-- The left-shift amount `d' - d - 1` is nonneg, where `d' = c >> s` (the new
`d`) and `d = c >> (s+1)` (the incoming `e`), for `0 ≤ s < c.bit_length()`. The
body's hardest precondition: it needs `d' ≥ 1` (from `s < L`, via `2^(L-1) ≤ c`)
and `d = d' // 2`. -/
theorem iter_lshift_nonneg {c s d : ℤ} (hc : 0 ≤ c) (hs_nn : 0 ≤ s)
    (hs_lt : s < pyBitLength c) (hd : d = Int.fdiv c (2 ^ (s + 1).toNat)) :
    0 ≤ Int.fdiv c (2 ^ s.toNat) - d - 1 := by
  set d' := Int.fdiv c (2 ^ s.toNat) with hd'
  -- d = d' // 2
  have hd2 : d = Int.fdiv d' 2 := by rw [hd, hd']; exact iter_d_halving hs_nn
  -- d' ≥ 1, from 2^s.toNat ≤ c
  have hd'_ge1 : 1 ≤ d' := by
    rw [hd', Int.le_fdiv_iff_mul_le (by positivity), one_mul]
    obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc
    rw [show pyBitLength (↑cn : ℤ) = ↑(natBitLength cn) from by
          simp [pyBitLength]] at hs_lt
    have hbl_pos : 0 < natBitLength cn := by omega
    have hcn_pos : 0 < cn := natBitLength_pos_iff.mp hbl_pos
    have hbound : 2 ^ (natBitLength cn - 1) ≤ cn := two_pow_pred_natBitLength_le hcn_pos
    have hexp : s.toNat ≤ natBitLength cn - 1 := by omega
    calc (2 : ℤ) ^ s.toNat
        ≤ (2 : ℤ) ^ (natBitLength cn - 1) := by
          apply pow_le_pow_right₀ (by norm_num) hexp
      _ = ((2 ^ (natBitLength cn - 1) : ℕ) : ℤ) := by push_cast; rfl
      _ ≤ (↑cn : ℤ) := by exact_mod_cast hbound
  rw [hd2, Int.fdiv_eq_ediv_of_nonneg d' (by norm_num : (0 : ℤ) ≤ 2)]
  omega

/-- The right-shift amount `2c - d' - d + 1` is nonneg, where `d' = c >> s` (the
new `d`) and `d = c >> (s+1)` (the incoming `e`). Both shifts are `≤ c` (for
`0 ≤ c`), so the amount is `≥ 1`. -/
theorem iter_rshift_nonneg {c s d : ℤ} (hc : 0 ≤ c)
    (hd : d = Int.fdiv c (2 ^ (s + 1).toNat)) :
    0 ≤ 2 * c - Int.fdiv c (2 ^ s.toNat) - d + 1 := by
  have h1 : Int.fdiv c (2 ^ s.toNat) ≤ c := fdiv_le_self_of_nonneg hc (by positivity)
  have h2 : Int.fdiv c (2 ^ (s + 1).toNat) ≤ c := fdiv_le_self_of_nonneg hc (by positivity)
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

/-- One execution of the loop body. Reads line-for-line with the Python suite

    e = d; d = c >> s; a = (a << d-e-1) + (n >> (2c-d-e+1)) // a; s = s - 1

The persistent locals `s, d, a` are unpacked from the loop state up front, and
the four assignments follow in order (`e` is the incoming `d`; Lean
`let`-shadowing of `s` and `d` mirrors Python's rebinding). The shift-nonneg
facts `hK`, `hJ` (and `ha_pos`) are in scope, so the py-ops' default `by omega`
discharges their preconditions. `iterInv` is re-established for the new state.
Defined as a standalone `def` (not inline in the `pyWhile` call) so the
precondition proofs don't entangle with the measure-decrease goal. -/
def iterBody (c n : ℤ) (hc : 0 ≤ c) (hn : 0 ≤ n)
    (st : IterSigma c) (h : 0 ≤ st.val.s) : IterSigma c :=
  -- the persistent Python locals, unpacked from the loop state
  let s := st.val.s
  let d := st.val.d
  let a := st.val.a
  -- invariant facts the body's preconditions consume
  have hs_nn  : 0 ≤ s                              := h
  have hd_eq  : d = Int.fdiv c (2 ^ (s + 1).toNat) := st.property.2.1
  have hs_lt  : s < pyBitLength c                  := st.property.1
  have ha_pos : 0 < a                              := st.property.2.2
  -- one pass of the loop body, line for line with the Python:
  --   e = d; d = c >> s; a = (a << d-e-1) + (n >> (2*c-d-e+1)) // a; s = s - 1
  let e := d
  let d := c py>> s
  have hK : 0 ≤ d - e - 1         := iter_lshift_nonneg hc hs_nn hs_lt hd_eq
  have hJ : 0 ≤ 2 * c - d - e + 1 := iter_rshift_nonneg hc hd_eq
  let a := (a py<< (d - e - 1)) + (n py>> (2 * c - d - e + 1)) py// a
  let s := s - 1
  ⟨{ s := s, d := d, a := a },
   ⟨by show st.val.s - 1 < pyBitLength c; omega,
    by show Int.fdiv c (2 ^ st.val.s.toNat) = Int.fdiv c (2 ^ (st.val.s - 1 + 1).toNat);
       rw [show (st.val.s - 1 + 1 : ℤ) = st.val.s by ring],
    isqrtIterative_body_pos ha_pos hn hK hJ⟩⟩

/-- The body decrements `s`. (Drives the measure-decrease proof.) -/
@[simp] theorem iterBody_s {c n : ℤ} {hc : 0 ≤ c} {hn : 0 ≤ n}
    {st : IterSigma c} {h : 0 ≤ st.val.s} :
    (iterBody c n hc hn st h).val.s = st.val.s - 1 := rfl

/-- The body sets `d` to `c >> s`. -/
@[simp] theorem iterBody_d {c n : ℤ} {hc : 0 ≤ c} {hn : 0 ≤ n}
    {st : IterSigma c} {h : 0 ≤ st.val.s} :
    (iterBody c n hc hn st h).val.d = Int.fdiv c (2 ^ st.val.s.toNat) := rfl

/-- The body's new `a`, in raw `Int.fdiv`/`*` form (the py-ops unfolded). With
`d' = c >> s` the new `a` is `a·2^(d'-e-1) + ⌊⌊n/2^(2c-d'-e+1)⌋/a⌋` (`e` the old
`d`); the correctness proof rewrites this into one `key_isqrt_lemma` step. -/
@[simp] theorem iterBody_a {c n : ℤ} {hc : 0 ≤ c} {hn : 0 ≤ n}
    {st : IterSigma c} {h : 0 ≤ st.val.s} :
    (iterBody c n hc hn st h).val.a =
      st.val.a * 2 ^ (Int.fdiv c (2 ^ st.val.s.toNat) - st.val.d - 1).toNat
        + Int.fdiv (Int.fdiv n
            (2 ^ (2 * c - Int.fdiv c (2 ^ st.val.s.toNat) - st.val.d + 1).toNat))
            st.val.a := rfl

/-! ## The iterative isqrt -/

/-- The `while s >= 0` loop of `isqrtIterative`, factored out as a standalone def
returning the final loop state (bundled with `¬ 0 ≤ s`, i.e. the loop has
stopped). Extracting it lets the correctness proof `unfold` this name and hand
the bare `pyWhile` application to `pyWhile_invariant` — exactly the
`countDownPos` pattern in `Tests/While.lean` — without having to reproduce the
opaque measure-decrease proof term. The measure is `(s + 1).toNat` rather than
`s.toNat`: the loop runs down to `s = -1`, where `s.toNat` would stall at the
final `0 → -1` step. -/
def isqrtIterativeLoop (c n : ℤ) (hc : 0 ≤ c) (hn : 0 ≤ n) :
    { st : IterSigma c // ¬ (0 ≤ st.val.s) } :=
  pyWhile
    (⟨{ s := pyBitLength c - 1, d := 0, a := 1 },
      ⟨by show pyBitLength c - 1 < pyBitLength c; omega,
       by show (0 : ℤ) = Int.fdiv c (2 ^ (pyBitLength c - 1 + 1).toNat);
          rw [show (pyBitLength c - 1 + 1 : ℤ) = pyBitLength c by ring]; exact (seed_d_eq hc).symm,
       one_pos⟩⟩ : IterSigma c)
    (fun st => 0 ≤ st.val.s)
    (iterBody c n hc hn)
    (fun st => (st.val.s + 1).toNat)
    (fun st h => by simp_wf; omega)

/-- Integer square root, iterative form (the rewritten Python target above).

Precondition `0 ≤ n`. `n = 0` is special-cased to `0` (the loop would otherwise
shift by a negative amount), mirroring the recursive `isqrt`. For `n ≥ 1` the
`while s >= 0` loop (`isqrtIterativeLoop`) is the faithful `pyWhile` translation;
the final line returns `a - 1` or `a` exactly as the Python
`return a - 1 if a * a > n else a`. -/
def isqrtIterative (n : ℤ) (n_nonneg : 0 ≤ n := by omega) : ℤ :=
  if _ : n = 0 then 0
  else
    let c := (pyBitLength n - 1) py// 2
    have hc : 0 ≤ c := isqrt_c_nonneg (by omega)
    let a := (isqrtIterativeLoop c n hc n_nonneg).val.val.a
    if a * a > n then a - 1 else a
