/-
Library root for the **definitions** component — the trust surface. Imports every
module a reader must read and check against Python: the `Except`-returning Python
operations, `bit_length`, the two `isqrt` translations, the integer-square-root
specification predicate, and the top-level correctness contract `isCorrectIsqrt`.
This component depends only on itself (and core/Mathlib), never on
`Isqrt.Proofs.*` or `Isqrt.Tests.*`.
-/

import Isqrt.Definitions.PythonOps
import Isqrt.Definitions.IntegerSquareRoot
import Isqrt.Definitions.Recursive
import Isqrt.Definitions.Iterative
import Isqrt.Definitions.Spec
