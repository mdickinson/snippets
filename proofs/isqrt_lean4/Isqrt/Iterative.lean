/-
Python's `math` module defines an `isqrt` function that computes the integer
part of the square root of a nonnegative integer input. The implementation of
`math.isqrt` is in C, but the comments in the C source include equivalent
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
- Recompute both shift amounts from the loop variable: `e = c >> (s + 1)` and
  `d = c >> s`, rather than threading `e = d` from the previous iteration. The two
  agree — the loop counts down, so the iteration before `s` processed `s + 1`, where
  `d` was `c >> (s + 1)` — and this leaves the body self-contained (no carried `d`).
- Remove the implicit bool-to-int conversion in the final return.
- Place the main body in an else branch.


    def isqrt(n: int) -> int:
        """For nonnegative n, find a satisfying a * a <= n < (a + 1) * (a + 1)."""
        if n == 0:
            return 0
        else:
            c = (n.bit_length() - 1) // 2

            a = 1
            for s in reversed(range(c.bit_length())):
                e = c >> (s + 1)
                d = c >> s
                a = (a << d - e - 1) + (n >> (2 * c - d - e + 1)) // a

            return a - 1 if a * a > n else a


This rewritten version is our target for translation into Lean.

The `for s in reversed(range(c.bit_length()))` loop translates into Lean's own
`for … in … do` notation, in the identity monad (`Id.run do`):

- the reversed range `reversed(range(L))` is the list `(List.range L).reverse`;
- `for h : s in …` binds the membership proof `h : s ∈ …`, which yields the loop
  variable's bound `s < L` (the `for`-with-proof form desugars to `forIn'`);
- the rebindable Python local `a` is a `let mut`, typed as the subtype
  `{a : ℤ // 0 < a}` so the running invariant (the `py// a` divisor is nonzero)
  rides along with the value across iterations.

`e` and `d` are loop-local, recomputed from `s`. The shift-nonneg facts `hK`, `hJ`
(and the carried `a > 0`) are in scope inside the loop body, so the py-ops' default
`by omega` discharges their preconditions.

Correctness for this form is proved in `Isqrt.IterativeCorrectness`: it reduces
the `do`/`forIn'` loop to a `List.foldl` over the reversed range via the
`Init.Data.List.Monadic` bridge lemma `List.forIn'_pure_yield_eq_foldl`, then
runs a position-indexed fold invariant — the same `key_isqrt_lemma` step the
recursive proof uses.
-/

import Isqrt.PythonOps
import Isqrt.BitLengthLemmas
import Isqrt.RecursionDepth

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

/-! ## The iterative isqrt -/

/-- Integer square root, iterative form (the rewritten Python target above).

Precondition `0 ≤ n`. `n = 0` is special-cased to `0` (the loop would otherwise
shift by a negative amount), mirroring the recursive `isqrt`. For `n ≥ 1` the
`for s in reversed(range(c.bit_length()))` loop is Lean's `for … in … do` over
`(List.range L).reverse` in the `Id` monad, with the running `a` a `let mut`; the
loop body reads line-for-line with the Python suite

    e = c >> (s + 1); d = c >> s; a = (a << d-e-1) + (n >> (2c-d-e+1)) // a

and the final line returns `a - 1` or `a` exactly as the Python
`return a - 1 if a * a > n else a`. -/
def isqrtIterative (n : ℤ) (n_nonneg : 0 ≤ n := by omega) : ℤ := Id.run do
  if _ : n = 0 then
    return 0
  else
    let c := (pyBitLength n - 1) py// 2
    have hc : 0 ≤ c := isqrt_c_nonneg (by omega)
    -- the running approximation `a`, carrying its positivity invariant
    let mut a : {a : ℤ // 0 < a} := ⟨1, one_pos⟩
    for h : s in (List.range (pyBitLength c).toNat).reverse do
      -- the loop variable's bound, read off the membership proof `h`
      have hsL : s < (pyBitLength c).toNat := List.mem_range.mp (List.mem_reverse.mp h)
      let av := a.val
      have ha_pos : 0 < av := a.property
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
      a := ⟨(av py<< (d - e - 1)) + (n py>> (2 * c - d - e + 1)) py// av,
            pyLshift_add_pyFloordiv_pos ha_pos n_nonneg hK hJ⟩
    let aFinal := a.val
    return (if aFinal * aFinal > n then aFinal - 1 else aFinal)
