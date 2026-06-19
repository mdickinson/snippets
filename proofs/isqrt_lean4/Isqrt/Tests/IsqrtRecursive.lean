/-
Direct actual-equals-expected-style tests for `isqrtRecursive`.
-/

import Isqrt.Definitions.IsqrtRecursive
import Isqrt.Tests.Assertions
import Isqrt.Tests.Vectors

#guard isqrtCases.all fun (n, expected) => assertReturns (isqrtRecursive n) expected
#guard assertRaisesValueError "isqrt() argument must be nonnegative" (isqrtRecursive (-1))
