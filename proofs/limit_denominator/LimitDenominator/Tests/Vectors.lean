module

/-!
The test vector for `limit_denominator`: actual-versus-expected cases, with every expected value
checked against `Fraction.limit_denominator` in CPython.
-/

@[expose] public section

/--
Tuples `(m, n, l, r, s)`: the closest fraction to `m / n` with denominator at most `l` is `r / s`.
-/
def limitDenominatorCases : List (Int × Int × Int × Int × Int) :=
  [ -- The three examples from the `Fraction.limit_denominator` documentation, with π's decimal
    -- expansion spelled out as the fraction the `Fraction` constructor would build.
    (3141592653589793, 1000000000000000, 10, 22, 7),
    (3141592653589793, 1000000000000000, 100, 311, 99),
    (4321, 8765, 10000, 4321, 8765),
    (-3141592653589793, 1000000000000000, 10, -22, 7),
    (-4321, 8765, 10000, -4321, 8765),
    -- Targets that are not in lowest terms: the result still is.
    (6, 4, 10, 3, 2),
    (100, 40, 3, 5, 2),
    -- An integer target, which leaves the loop immediately with `b = 0`, so that the
    -- short-circuiting `and` is what stops the loop condition dividing by zero.
    (7, 1, 5, 7, 1),
    (-7, 1, 5, -7, 1),
    (0, 5, 3, 0, 1),
    -- A limit of one rounds to an integer, breaking a halfway tie towards the smaller fraction.
    -- These are the only cases where the two candidates share a denominator.
    (1, 2, 1, 0, 1),
    (-1, 2, 1, -1, 1),
    (5, 2, 1, 2, 1),
    (-5, 2, 1, -3, 1),
    -- Halfway ties at a larger limit, broken towards the smaller denominator: `5/4` is midway
    -- between `1/1` and `3/2`, and `1/1` is returned even though it is the larger of the two.
    (5, 4, 2, 1, 1),
    (-5, 4, 2, -1, 1),
    -- Cases returning the extended candidate rather than the loop candidate.
    (7, 5, 3, 4, 3),
    (-7, 5, 3, -4, 3),
    -- Cases returning the loop candidate outright.
    (3, 8, 2, 1, 2),
    (17, 12, 5, 7, 5),
    -- The limit is already large enough to represent the target exactly.
    (22, 7, 7, 22, 7),
    (22, 7, 1000, 22, 7) ]

end
