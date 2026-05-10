/-
Sanity checks for PythonOps definitions.

These #guard statements verify that our Lean definitions produce
the same results as the corresponding Python operations on concrete
values. A failing #guard causes a build error.
-/

import IsqrtLean4.PythonOps

/-! ## pyFloorDiv -/

-- positive denominator
#guard pyFloorDiv 7 2 (by omega) == 3
#guard pyFloorDiv (-7) 2 (by omega) == -4    -- floor division rounds toward -∞
#guard pyFloorDiv 0 3 (by omega) == 0

-- negative denominator
#guard pyFloorDiv 7 (-2) (by omega) == -4    -- 7 // (-2) == -4 in Python
#guard pyFloorDiv (-7) (-2) (by omega) == 3  -- (-7) // (-2) == 3 in Python

/-! ## pyRShift -/

#guard pyRShift 100 3 (by omega) == 12       -- 100 >> 3 == 100 // 8

/-! ## pyLShift -/

#guard pyLShift 3 4 (by omega) == 48         -- 3 << 4 == 3 * 16

/-! ## pyBitLength -/

#guard pyBitLength 0 == 0
#guard pyBitLength 1 == 1
#guard pyBitLength 255 == 8
#guard pyBitLength 256 == 9
#guard pyBitLength (-256) == 9               -- bit_length of abs
