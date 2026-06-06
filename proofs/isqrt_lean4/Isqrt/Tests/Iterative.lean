/-
Sanity checks for the iterative isqrt.

These #guard statements verify that `isqrtIterative` produces the correct
integer square root for a selection of concrete values, matching `isqrt`
(see `Tests/Isqrt.lean`). A failing #guard causes a build error.
-/

import Isqrt.Iterative

/-! ## isqrtIterative -/

-- zero (special-cased before the loop)
#guard isqrtIterative 0 == 0

-- perfect squares
#guard isqrtIterative 1 == 1
#guard isqrtIterative 4 == 2
#guard isqrtIterative 9 == 3
#guard isqrtIterative 16 == 4
#guard isqrtIterative 100 == 10
#guard isqrtIterative 10000 == 100

-- non-perfect squares (returns floor of sqrt)
#guard isqrtIterative 2 == 1
#guard isqrtIterative 3 == 1
#guard isqrtIterative 5 == 2
#guard isqrtIterative 8 == 2
#guard isqrtIterative 15 == 3
#guard isqrtIterative 17 == 4
#guard isqrtIterative 99 == 9
#guard isqrtIterative 101 == 10

-- just below and just above a perfect square
#guard isqrtIterative 24 == 4
#guard isqrtIterative 25 == 5
#guard isqrtIterative 26 == 5

-- larger value
#guard isqrtIterative 999999 == 999
#guard isqrtIterative 1000000 == 1000
#guard isqrtIterative 1000001 == 1000
