/-
Sanity checks for PythonOps definitions.

These #guard statements verify that our Lean definitions produce
the same results as the corresponding Python operations on concrete
values. A failing #guard causes a build error.
-/

import IsqrtLean4.PythonOps

open PyOps

/-! ## pyFloorDiv (//) -/

-- positive denominator
#guard 7 // 2 == 3
#guard (-7) // 2 == -4                       -- floor division rounds toward -∞
#guard 0 // 3 == 0

-- negative denominator
#guard 7 // (-2) == -4                       -- 7 // (-2) == -4 in Python
#guard (-7) // (-2) == 3                     -- (-7) // (-2) == 3 in Python

/-! ## pyRShift (>>) -/

-- Use pyRShift directly here to avoid ambiguity with Lean's built-in >>
#guard pyRShift 100 3 == 12                  -- 100 >> 3 == 100 // 8
#guard pyRShift (-100) 3 == -13              -- (-100) >> 3 == -100 // 8 == -13 in Python

/-! ## pyLShift (<<) -/

#guard 3 << 4 == 48                          -- 3 << 4 == 3 * 16

/-! ## pyBitLength -/

#guard pyBitLength 0 == 0
#guard pyBitLength 1 == 1
#guard pyBitLength 255 == 8
#guard pyBitLength 256 == 9
#guard pyBitLength (-256) == 9               -- bit_length of abs
