/-
Definitions of `isqrt_aux` and `isqrt`, matching the Python code:

    def isqrt_aux(c, n):
        if c == 0:
            return 1
        else:
            k = (c - 1) // 2
            a = isqrt_aux(c // 2, n >> (2 * k + 2))
            return (a << k) + (n >> (k + 2)) // a

    def isqrt(n):
        if n == 0:
            return 0
        else:
            a = isqrt_aux((n.bit_length() - 1) // 2, n)
            return a - 1 if n < a * a else a

Both functions carry proof-carrying preconditions. `isqrt_aux` returns a
subtype `{ a : ℤ // 0 < a }` so that the positivity of the result is
available for the `// a` division in the recursive case.
-/

import IsqrtLean4.PythonOps
import IsqrtLean4.FDivLemmas
import IsqrtLean4.BitLengthLemmas

/-! ## isqrt_aux -/

open PyOps in
/-- The return expression `(a << k) + (n >> (k+2)) // a` is positive
when `a > 0`, `n ≥ 0`, and `k ≥ 0`. -/
private theorem isqrt_aux_return_pos {a n k : ℤ}
    (a_pos : 0 < a) (n_nonneg : 0 ≤ n)
    (k_nonneg : 0 ≤ k) :
    0 < (a << k) + (n >> (k + 2)) // a := by
  simp [pyLShift_def, pyFloorDiv_def, pyRShift_def]
  have : 0 < a * 2 ^ k.toNat := Int.mul_pos a_pos (by positivity)
  have : 0 ≤ (n.fdiv (2 ^ (k + 2).toNat)).fdiv a :=
    Int.fdiv_nonneg (Int.fdiv_nonneg n_nonneg (by positivity)) (le_of_lt a_pos)
  omega

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
def isqrt_aux (c n : ℤ) (c_nonneg : 0 ≤ c := by omega) (n_nonneg : 0 ≤ n := by omega) : { a : ℤ // 0 < a } := open PyOps in
  if _ : c = 0 then
    ⟨1, by omega⟩
  else
    let k := (c - 1) // 2
    have k_nonneg : 0 ≤ k := pyFloorDiv_nonneg (by omega) (by omega)
    let d := c // 2
    have d_nonneg : 0 ≤ d := pyFloorDiv_nonneg c_nonneg (by omega)
    let ⟨a, a_pos⟩ := isqrt_aux d (n >> (2 * k + 2))
                                 d_nonneg (pyRShift_nonneg n_nonneg)
    let b := (a << k) + (n >> (k + 2)) // a
    have b_pos : 0 < b := isqrt_aux_return_pos a_pos n_nonneg k_nonneg
    ⟨b, b_pos⟩
termination_by c.toNat
decreasing_by
  simp_wf
  exact fdiv_two_decreasing c_nonneg ‹¬c = 0›

/-! ## isqrt -/

open PyOps in
/-- The recursion depth `(n.bit_length() - 1) // 2` is nonneg for nonzero `n`. -/
private theorem isqrt_c_nonneg {n : ℤ} (hn : n ≠ 0) :
    0 ≤ (pyBitLength n - 1) // 2 :=
  pyFloorDiv_nonneg (by have := pyBitLength_pos hn; omega) (by omega)

/-- Integer square root, matching CPython's `math.isqrt`.

Precondition: `0 ≤ n`.

Returns the largest integer `a` such that `a² ≤ n`. -/
def isqrt (n : ℤ) (n_nonneg : 0 ≤ n := by omega) : ℤ := open PyOps in
  if _ : n = 0 then
    0
  else
    let c := (pyBitLength n - 1) // 2
    let a := (isqrt_aux c n (isqrt_c_nonneg (by omega))).val
    if n < a * a then a - 1 else a
