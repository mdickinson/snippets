/-
Definitions of `isqrt_aux` and `isqrt`, matching the Python code:

    def isqrt_aux(c, n):
        if c == 0:
            return 1
        else:
            k = (c - 1) // 2
            a = isqrt_aux(c // 2, n >> 2*k + 2)
            return (a << k) + (n >> k+2) // a

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

/-- Recursive auxiliary function for integer square root.

Preconditions:
- `0 ≤ c`: the recursion parameter (floor of log₄(n) for valid inputs)
- `0 ≤ n`: the value whose square root we approximate

Returns `{ a : ℤ // 0 < a }`: the result is always positive, which is
needed for the `// a` division in the recursive case. -/
def isqrt_aux (c n : ℤ) (_hc : 0 ≤ c) (_hn : 0 ≤ n) : { a : ℤ // 0 < a } :=
  if hc0 : c = 0 then
    ⟨1, by omega⟩
  else
    have hc_pos : 0 < c := lt_of_le_of_ne _hc (Ne.symm hc0)
    let k := pyFloorDiv (c - 1) 2 (by omega)
    have hk_nonneg : 0 ≤ k := by
      simp [k, pyFloorDiv_def]
      exact Int.fdiv_nonneg (by omega) (by omega)
    have h2k2 : 0 ≤ 2 * k + 2 := by omega
    have hk2 : 0 ≤ k + 2 := by omega
    have hn' : 0 ≤ pyRShift n (2 * k + 2) h2k2 := by
      simp [pyRShift_def]
      exact Int.fdiv_nonneg _hn (by positivity)
    have hc2 : 0 ≤ pyFloorDiv c 2 (by omega) := by
      simp [pyFloorDiv_def]
      exact Int.fdiv_nonneg (by omega) (by omega)
    let ⟨a, ha⟩ := isqrt_aux (pyFloorDiv c 2 (by omega))
                              (pyRShift n (2 * k + 2) h2k2) hc2 hn'
    ⟨pyLShift a k hk_nonneg + pyFloorDiv (pyRShift n (k + 2) hk2) a (ne_of_gt ha),
     by
      simp [pyLShift_def, pyFloorDiv_def, pyRShift_def]
      have : 0 < a * 2 ^ k.toNat := Int.mul_pos ha (by positivity)
      have : 0 ≤ (n.fdiv (2 ^ (k + 2).toNat)).fdiv a :=
        Int.fdiv_nonneg (Int.fdiv_nonneg _hn (by positivity)) (le_of_lt ha)
      omega⟩
termination_by c.toNat
decreasing_by
  simp_wf
  rw [Int.fdiv_eq_ediv_of_nonneg c (by omega : (0 : ℤ) ≤ 2)]
  omega

/-! ## isqrt -/

/-- Integer square root, matching CPython's `math.isqrt`.

Precondition: `0 ≤ n`.

Returns the largest integer `a` such that `a² ≤ n`. -/
def isqrt (n : ℤ) (_hn : 0 ≤ n) : ℤ :=
  if hn0 : n = 0 then
    0
  else
    have hn_pos : 0 < n := lt_of_le_of_ne _hn (Ne.symm hn0)
    have hbl_pos : 0 < pyBitLength n := by
      simp [pyBitLength_def]
      rw [Nat.pos_iff_ne_zero]
      exact (natBitLength_pos_iff.mpr (by omega : 0 < n.natAbs)).ne'
    have hbl_nn : 0 ≤ pyBitLength n - 1 := by omega
    let a := (isqrt_aux (pyFloorDiv (pyBitLength n - 1) 2 (by omega))
                        n
                        (by simp [pyFloorDiv_def]
                            exact Int.fdiv_nonneg hbl_nn (by omega))
                        (le_of_lt hn_pos)).val
    if n < a * a then a - 1 else a
