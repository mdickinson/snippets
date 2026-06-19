import Isqrt.Tests.PythonPrimitives
import Isqrt.Tests.IsqrtIterative
import Isqrt.Tests.IsqrtRecursive

/-!
Aggregator module for the `#guard`-based sanity checks: the Python primitives and
the two `isqrt` translations. The shared `Isqrt.Tests.Assertions` helpers and
`Isqrt.Tests.Vectors` test vector come in transitively. This component depends on
`Isqrt.Definitions.*`, never on `Isqrt.Proofs.*`.
-/
