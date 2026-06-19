/-
The shared test vector for the integer square root, used by both
`Isqrt.Tests.IsqrtIterative` and `Isqrt.Tests.IsqrtRecursive`.
-/

/-- Pairs (isqrt input, expected output). -/
def isqrtCases : List (Int × Int) :=
  [ (0, 0), (1, 1),
    (2, 1), (3, 1),                  -- below 2² = 4
    (4, 2), (5, 2), (8, 2),          -- 4 = 2², up to just below 3²
    (9, 3), (15, 3),                 -- 9 = 3², up to just below 4²
    (16, 4), (24, 4),                -- 16 = 4², up to just below 5²
    (25, 5), (26, 5),                -- 25 = 5², just above
    (999999, 999), (1000000, 1000), (1000001, 1000),
    (10 ^ 1000, 10 ^ 500) ]
