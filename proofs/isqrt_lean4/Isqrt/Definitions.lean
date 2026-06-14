/-
Library root for the **definitions** component — the trust surface. Imports every
module a reader must read and check against Python: the exception vocabulary
(`PyException` and the return-or-raise helpers), the `Except`-returning Python
operations, `bit_length`, the two `isqrt` translations, and the specification
(the postcondition predicate `isIntegerSquareRoot` and the top-level correctness
contract `isCorrectIsqrt`). This component depends only on itself and Lean
core — no Mathlib — and never on `Isqrt.Proofs.*` or `Isqrt.Tests.*`.
-/

import Isqrt.Definitions.Exceptions
import Isqrt.Definitions.PythonOps
import Isqrt.Definitions.Recursive
import Isqrt.Definitions.Iterative
import Isqrt.Definitions.Specification
