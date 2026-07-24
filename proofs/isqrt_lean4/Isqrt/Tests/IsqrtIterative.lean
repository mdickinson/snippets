module

meta import Isqrt.Definitions.IsqrtIterative
meta import Isqrt.Tests.Assertions
meta import Isqrt.Tests.Vectors

/-!
Direct actual-equals-expected-style tests for `isqrtIterative`.
-/

#guard isqrtCases.all fun (n, expected) => assertReturns (isqrtIterative n) expected
#guard assertRaisesValueError "isqrt() argument must be nonnegative" (isqrtIterative (-1))
