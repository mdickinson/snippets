/-
Direct actual-equals-expected-style tests for `isqrtRecursive`.
-/

module

meta import Isqrt.Definitions.IsqrtRecursive
meta import Isqrt.Tests.Assertions
meta import Isqrt.Tests.Vectors

#guard isqrtCases.all fun (n, expected) => assertReturns (isqrtRecursive n) expected
#guard assertRaisesValueError "isqrt() argument must be nonnegative" (isqrtRecursive (-1))
