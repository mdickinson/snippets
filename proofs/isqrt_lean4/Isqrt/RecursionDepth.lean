/-
The recursion depth shared by both isqrt formulations.

Both `isqrt` (recursive, `Isqrt.Algorithm`) and `isqrtIterative`
(`Isqrt.Iterative`) open by computing `c = (n.bit_length() - 1) // 2` and rely on
it being nonnegative. Factoring that single fact out here lets each algorithm
module import it without depending on the other.
-/

import Isqrt.PythonOps
import Isqrt.BitLengthLemmas

/-- The recursion depth `(n.bit_length() - 1) py// 2` is nonneg for nonzero `n`. -/
theorem isqrt_c_nonneg {n : ℤ} (hn : n ≠ 0) :
    0 ≤ (pyBitLength n - 1) py// 2 :=
  pyFloordiv_nonneg (by have := pyBitLength_pos hn; omega) (by omega)
