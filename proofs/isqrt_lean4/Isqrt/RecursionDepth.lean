/-
The recursion depth shared by both isqrt formulations.

Both `isqrt` (recursive, `Isqrt.Algorithm`) and `isqrtIterative`
(`Isqrt.Iterative`) open by computing `c = (n.bit_length() - 1) // 2` and rely on
it being nonnegative. Factoring that single fact out here lets each algorithm
module import it without depending on the other.
-/

import Isqrt.BitLengthLemmas

/-- The recursion depth `⌊(n.bit_length() - 1) / 2⌋` is nonneg for nonzero `n`.
Stated in pure `Int.fdiv` form (the `Except` `//`, `pyFloordiv`, reduces to it on
its `.ok` branch), so both the iterative and recursive isqrt share it. -/
theorem isqrt_c_nonneg {n : ℤ} (hn : n ≠ 0) :
    0 ≤ Int.fdiv (pyBitLength n - 1) 2 :=
  Int.fdiv_nonneg (by have := pyBitLength_pos hn; omega) (by omega)
