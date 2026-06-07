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
needs to typecheck. The py-op precondition proofs are kept out of the `pyWhile`
call as top-level lemmas: an inline `by` inside the `⟨val, proof⟩` constructor
hits an elaboration-order bug where the proof metavariable entangles with the
measure-decrease goal (surfacing as a spurious "no goals to be solved").
Correctness lives in `Isqrt.IterativeCorrectness`.
-/

import Isqrt.PythonOps
import Isqrt.BitLengthLemmas
import Isqrt.RecursionDepth
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
shift from the *previous* iteration.

This is a `structure` rather than a bare conjunction so that the `py>>` in
`hd_eq` can discharge its `0 ≤ s + 1` precondition from the earlier `hs_lb`
field (a plain `∧` cannot share a proof between conjuncts). `hs_lb` is the loop
variable's lower bound, reached (`s = -1`) at loop exit; its full *nonnegativity*
during the loop comes from the loop condition `0 ≤ s`, so that is not bundled
here — nor are the near-√ property and the size condition. -/
structure iterInv (c : ℤ) (st : IterState) : Prop where
  /-- `s` never drops below `-1`, so the shift amount `s + 1` is nonneg. -/
  hs_lb : -1 ≤ st.s
  /-- `s` stays below `c.bit_length()`. -/
  hs_lt : st.s < pyBitLength c
  /-- `d` is `c` right-shifted by the previous iteration's amount. -/
  hd_eq : st.d = c py>> (st.s + 1)
  /-- `a` is positive (the `py// a` precondition). -/
  ha_pos : 0 < st.a

/-- The loop-state type handed to `pyWhile`: states carrying `iterInv c`. -/
abbrev IterSigma (c : ℤ) := { st : IterState // iterInv c st }

/-! ## Body precondition lemmas (top-level named lemmas, not inline `by`) -/

/-- The left-shift amount `d' - d - 1` is nonneg, where `d' = c >> s` (the new
`d`) and `d = c >> (s+1)` (the incoming `e`), for `0 ≤ s < c.bit_length()`. The
body's hardest precondition: it needs `d' ≥ 1` (from `s < L`,
`one_le_pyRshift_of_lt_pyBitLength`) and the halving link `d = d' // 2`
(`pyRshift_succ`). -/
theorem iter_lshift_nonneg {c s d : ℤ} (hc : 0 ≤ c) (hs_nn : 0 ≤ s)
    (hs_lt : s < pyBitLength c) (hd : d = c py>> (s + 1)) :
    0 ≤ (c py>> s) - d - 1 := by
  -- d = (c >> s) // 2, the halving link
  have hhalve : d = (c py>> s) py// 2 := by rw [hd]; exact pyRshift_succ c s hs_nn
  -- c >> s ≥ 1, since s < c.bit_length()
  have hge1 : 1 ≤ c py>> s := one_le_pyRshift_of_lt_pyBitLength hc hs_nn hs_lt
  -- and a floor-half is bounded by its argument
  have hmul : ((c py>> s) py// 2) * 2 ≤ c py>> s := pyFloordiv_mul_le_self (c py>> s) 2 (by norm_num)
  have hnn : 0 ≤ (c py>> s) py// 2 := pyFloordiv_nonneg (by omega) (by norm_num)
  rw [hhalve]; omega

/-- The right-shift amount `2c - d' - d + 1` is nonneg, where `d' = c >> s` (the
new `d`) and `d = c >> (s+1)` (the incoming `e`). Both shifts are `≤ c` (for
`0 ≤ c`), so the amount is `≥ 1`. -/
theorem iter_rshift_nonneg {c s d : ℤ} (hc : 0 ≤ c) (hs_nn : 0 ≤ s)
    (hd : d = c py>> (s + 1)) :
    0 ≤ 2 * c - (c py>> s) - d + 1 := by
  have h1 : c py>> s ≤ c := pyRshift_le_self hc hs_nn
  have h2 : c py>> (s + 1) ≤ c := pyRshift_le_self hc (by omega)
  rw [hd]; omega

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
  have hs_nn  : 0 ≤ s              := h
  have hd_eq  : d = c py>> (s + 1) := st.property.hd_eq
  have hs_lt  : s < pyBitLength c  := st.property.hs_lt
  have ha_pos : 0 < a              := st.property.ha_pos
  -- one pass of the loop body, line for line with the Python:
  --   e = d; d = c >> s; a = (a << d-e-1) + (n >> (2*c-d-e+1)) // a; s = s - 1
  let e := d
  let d := c py>> s
  have hK : 0 ≤ d - e - 1         := iter_lshift_nonneg hc hs_nn hs_lt hd_eq
  have hJ : 0 ≤ 2 * c - d - e + 1 := iter_rshift_nonneg hc hs_nn hd_eq
  let a := (a py<< (d - e - 1)) + (n py>> (2 * c - d - e + 1)) py// a
  let s := s - 1
  ⟨{ s := s, d := d, a := a },
   { hs_lb := by show (-1 : ℤ) ≤ st.val.s - 1; omega,
     hs_lt := by show st.val.s - 1 < pyBitLength c; omega,
     hd_eq := by
       show c py>> st.val.s = c py>> (st.val.s - 1 + 1)
       simp only [pyRshift_def]
       rw [show (st.val.s - 1 + 1 : ℤ) = st.val.s from by ring]
     ha_pos := pyLshift_add_pyFloordiv_pos ha_pos hn hK hJ }⟩

/-- The body decrements `s`. (Drives the measure-decrease proof.) -/
@[simp] theorem iterBody_s {c n : ℤ} {hc : 0 ≤ c} {hn : 0 ≤ n}
    {st : IterSigma c} {h : 0 ≤ st.val.s} :
    (iterBody c n hc hn st h).val.s = st.val.s - 1 := rfl

/-- The body sets `d` to `c >> s`. -/
@[simp] theorem iterBody_d {c n : ℤ} {hc : 0 ≤ c} {hn : 0 ≤ n}
    {st : IterSigma c} {h : 0 ≤ st.val.s} :
    (iterBody c n hc hn st h).val.d = c py>> st.val.s := rfl

/-- The body's new `a`, mirroring the Python `(a << d-e-1) + (n >> 2c-d-e+1) // a`
with `d = c >> s` and `e` the old `d`. The shift/divisor preconditions are passed
explicitly via the named lemmas (the infix operators' `by omega` default can't
discharge them); the correctness proof unfolds the py-ops with `*_def` and
rewrites the result into one `key_isqrt_lemma` step. -/
@[simp] theorem iterBody_a {c n : ℤ} {hc : 0 ≤ c} {hn : 0 ≤ n}
    {st : IterSigma c} {h : 0 ≤ st.val.s} :
    (iterBody c n hc hn st h).val.a =
      pyLshift st.val.a ((c py>> st.val.s) - st.val.d - 1)
          (iter_lshift_nonneg hc h st.property.hs_lt st.property.hd_eq)
        + pyFloordiv
            (pyRshift n (2 * c - (c py>> st.val.s) - st.val.d + 1)
              (iter_rshift_nonneg hc h st.property.hd_eq))
            st.val.a st.property.ha_pos.ne' := rfl

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
      { hs_lb := by
          have hbl := pyBitLength_nonneg c
          show (-1 : ℤ) ≤ pyBitLength c - 1; omega
        hs_lt := by show pyBitLength c - 1 < pyBitLength c; omega
        hd_eq := by
          have hbl := pyBitLength_nonneg c
          show (0 : ℤ) = c py>> (pyBitLength c - 1 + 1)
          simp only [pyRshift_def]
          rw [show (pyBitLength c - 1 + 1 : ℤ) = pyBitLength c from by ring]
          exact (pyRshift_pyBitLength_eq_zero hc).symm
        ha_pos := one_pos }⟩ : IterSigma c)
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
