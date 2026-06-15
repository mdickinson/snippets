/-
Library root for the **definitions** component. Imports the exception vocabulary, the
Python-operation mirrors, the iterative and recursive `isqrt` translations, and the
correctness specification. Depends only on the Lean core; no Mathlib dependence.
-/

import Isqrt.Definitions.Exceptions
import Isqrt.Definitions.PythonOps
import Isqrt.Definitions.Iterative
import Isqrt.Definitions.Recursive
import Isqrt.Definitions.Specification
