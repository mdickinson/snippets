/-
Python-compatible integer operations for use in Lean proofs.

Provides Lean definitions matching the semantics of Python's:
- `//` (floor division)
- `>>` (right shift)
- `<<` (left shift)
- `int.bit_length()`

Each operation that can raise an exception in Python requires a validity
proof at the call site (e.g., nonzero divisor, nonneg shift amount).
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
