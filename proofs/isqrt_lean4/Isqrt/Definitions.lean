/-
Library root for the **definitions** component — the trust surface. Imports every
module a reader must read and check against Python: the `Except`-returning Python
operations, `bit_length`, the two `isqrt` translations, and the integer-square-root
specification predicate. This component depends only on itself (and core/Mathlib),
never on `Isqrt.Proofs.*` or `Isqrt.Tests.*`.
-/

import Isqrt.Definitions.PythonOps
import Isqrt.Definitions.BitLength
import Isqrt.Definitions.IntegerSquareRoot
import Isqrt.Definitions.Algorithm
import Isqrt.Definitions.Iterative
