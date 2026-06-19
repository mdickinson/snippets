/-
Direct actual-equals-expected-style tests for `isqrtIterative`.
-/

import Isqrt.Definitions.IsqrtIterative
import Isqrt.Tests.Assertions
import Isqrt.Tests.Vectors

#guard isqrtCases.all fun (n, expected) => assertReturns (isqrtIterative n) expected
#guard assertRaisesValueError "isqrt() argument must be nonnegative" (isqrtIterative (-1))
