/-
Sanity checks for isqrt.

These #guard statements verify that isqrt produces the correct integer
square root for a selection of concrete values. A failing #guard causes
a build error.
-/

import IsqrtLean4.Isqrt

/-! ## isqrt -/

-- zero
#guard isqrt 0 (by omega) == 0

-- perfect squares
#guard isqrt 1 (by omega) == 1
#guard isqrt 4 (by omega) == 2
#guard isqrt 9 (by omega) == 3
#guard isqrt 16 (by omega) == 4
#guard isqrt 100 (by omega) == 10
#guard isqrt 10000 (by omega) == 100

-- non-perfect squares (returns floor of sqrt)
#guard isqrt 2 (by omega) == 1
#guard isqrt 3 (by omega) == 1
#guard isqrt 5 (by omega) == 2
#guard isqrt 8 (by omega) == 2
#guard isqrt 15 (by omega) == 3
#guard isqrt 17 (by omega) == 4
#guard isqrt 99 (by omega) == 9
#guard isqrt 101 (by omega) == 10

-- just below and just above a perfect square
#guard isqrt 24 (by omega) == 4
#guard isqrt 25 (by omega) == 5
#guard isqrt 26 (by omega) == 5

-- larger value
#guard isqrt 999999 (by omega) == 999
#guard isqrt 1000000 (by omega) == 1000
#guard isqrt 1000001 (by omega) == 1000
