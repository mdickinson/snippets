/-
Sanity checks for isqrt.

These #guard statements verify that isqrt produces the correct integer
square root for a selection of concrete values. A failing #guard causes
a build error.
-/

import Isqrt.Algorithm

/-! ## isqrt -/

-- zero
#guard isqrt 0 == 0

-- perfect squares
#guard isqrt 1 == 1
#guard isqrt 4 == 2
#guard isqrt 9 == 3
#guard isqrt 16 == 4
#guard isqrt 100 == 10
#guard isqrt 10000 == 100

-- non-perfect squares (returns floor of sqrt)
#guard isqrt 2 == 1
#guard isqrt 3 == 1
#guard isqrt 5 == 2
#guard isqrt 8 == 2
#guard isqrt 15 == 3
#guard isqrt 17 == 4
#guard isqrt 99 == 9
#guard isqrt 101 == 10

-- just below and just above a perfect square
#guard isqrt 24 == 4
#guard isqrt 25 == 5
#guard isqrt 26 == 5

-- larger value
#guard isqrt 999999 == 999
#guard isqrt 1000000 == 1000
#guard isqrt 1000001 == 1000
