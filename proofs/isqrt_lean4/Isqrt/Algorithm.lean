/-
Definitions of `isqrtAux` and `isqrt`, matching the Python code:

    def isqrt_aux(c: int, n: int) -> int:
        if c == 0:
            return 1
        else:
            k = (c - 1) // 2
            a = isqrt_aux(c // 2, n >> (2 * k + 2))
            return (a << k) + (n >> (k + 2)) // a

    def isqrt(n: int) -> int:
        if n == 0:
            return 0
        else:
            c = (n.bit_length() - 1) // 2
            a = isqrt_aux(c, n)
            return a - 1 if n < a * a else a

Both functions carry proof-carrying preconditions. `isqrtAux` returns a
subtype `{ a : ℤ // 0 < a }` so that the positivity of the result is
available for the `// a` division in the recursive case.

Correctness proofs live in `Isqrt.Correctness`.
-/

import Isqrt.PythonOps
import Isqrt.FDivLemmas
import Isqrt.BitLengthLemmas
import Isqrt.RecursionDepth
import Isqrt.KeyLemma
import Isqrt.SizeConditions

/-! ## isqrtAux -/

/-- The return expression `(a py<< k) + (n py>> (k+2)) py// a` is positive
when `a > 0`, `n ≥ 0`, and `k ≥ 0` — the `K = k`, `J = k+2` specialization of
`pyLshift_add_pyFloordiv_pos`. -/
private theorem isqrtAux_return_pos {a n k : ℤ}
    (a_pos : 0 < a) (n_nonneg : 0 ≤ n) (k_nonneg : 0 ≤ k) :
    0 < (a py<< k) + (n py>> (k + 2)) py// a :=
  pyLshift_add_pyFloordiv_pos a_pos n_nonneg k_nonneg (by omega)

/-- Floor-dividing a positive integer by 2 gives a strictly smaller
positive result — in the form needed by the termination checker. -/
private theorem fdiv_two_decreasing {c : ℤ} (hc_nonneg : 0 ≤ c) (hc_ne : ¬ c = 0) :
    c.fdiv 2 < c ∧ 0 < c := by
  rw [Int.fdiv_eq_ediv_of_nonneg c (by omega : (0 : ℤ) ≤ 2)]
  omega

/-- Recursive auxiliary function for integer square root.

Preconditions:
- `0 ≤ c`: the recursion parameter (floor of log₄(n) for valid inputs)
- `0 ≤ n`: the value whose square root we approximate

Returns `{ a : ℤ // 0 < a }`: the result is always positive, which is
needed for the `// a` division in the recursive case. -/
def isqrtAux (c n : ℤ) (c_nonneg : 0 ≤ c := by omega) (n_nonneg : 0 ≤ n := by omega) : { a : ℤ // 0 < a } :=
  if _ : c = 0 then
    ⟨1, by omega⟩
  else
    let k := (c - 1) py// 2
    have k_nonneg : 0 ≤ k := pyFloordiv_nonneg (by omega) (by omega)
    let d := c py// 2
    have d_nonneg : 0 ≤ d := pyFloordiv_nonneg c_nonneg (by omega)
    let ⟨a, a_pos⟩ := isqrtAux d (n py>> (2 * k + 2))
                                 d_nonneg (pyRshift_nonneg n_nonneg)
    let b := (a py<< k) + (n py>> (k + 2)) py// a
    have b_pos : 0 < b := isqrtAux_return_pos a_pos n_nonneg k_nonneg
    ⟨b, b_pos⟩
termination_by c.toNat
decreasing_by
  simp_wf
  exact fdiv_two_decreasing c_nonneg ‹¬c = 0›

/-! ## isqrt -/

/-- Integer square root, matching CPython's `math.isqrt`.

Precondition: `0 ≤ n`.

Returns the largest integer `a` such that `a² ≤ n`. -/
def isqrt (n : ℤ) (n_nonneg : 0 ≤ n := by omega) : ℤ :=
  if _ : n = 0 then
    0
  else
    let c := (pyBitLength n - 1) py// 2
    let a := (isqrtAux c n (isqrt_c_nonneg (by omega))).val
    if n < a * a then a - 1 else a
