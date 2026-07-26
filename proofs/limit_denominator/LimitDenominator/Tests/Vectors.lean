module

/-!
The test vectors for `limit_denominator`, one list per listing: actual-versus-expected cases,
with every expected value checked against `Fraction.limit_denominator` in CPython.
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
    -- A limit of one rounds to an integer, so a target midway between two consecutive integers
    -- ties at equal denominators — the only configuration in which that happens. The lesser of
    -- the two values is returned, which for a negative target is the one further from zero.
    (1, 2, 1, 0, 1),
    (-1, 2, 1, -1, 1),
    (5, 2, 1, 2, 1),
    (-5, 2, 1, -3, 1),
    -- Halfway ties at a larger limit, where the denominators differ and settle it on their own.
    -- `5/4` is midway between `1/1` and `3/2`, and `7/4` between `3/2` and `2/1`; the
    -- denominator-one candidate wins both, though it is the lesser value in the first and the
    -- greater in the second.
    (5, 4, 2, 1, 1),
    (-5, 4, 2, -1, 1),
    (7, 4, 2, 2, 1),
    (-7, 4, 2, -2, 1),
    -- Cases returning the extended candidate rather than the loop candidate.
    (7, 5, 3, 4, 3),
    (-7, 5, 3, -4, 3),
    -- Cases returning the loop candidate outright.
    (3, 8, 2, 1, 2),
    (17, 12, 5, 7, 5),
    -- The limit is already large enough to represent the target exactly.
    (22, 7, 7, 22, 7),
    (22, 7, 1000, 22, 7) ]

/--
Tuples `(m, n, l, r, s)` for the stdlib listing, whose target must be in lowest terms with a
positive denominator: the closest fraction to `m / n` with denominator at most `l` is `r / s`.
-/
def limitDenominatorStdlibCases : List (Int × Int × Int × Int × Int) :=
  [ -- The documentation's π examples, and their negations.
    (3141592653589793, 1000000000000000, 10, 22, 7),
    (3141592653589793, 1000000000000000, 100, 311, 99),
    (-3141592653589793, 1000000000000000, 10, -22, 7),
    (-3141592653589793, 1000000000000000, 100, -311, 99),
    -- The fast path returns the target unaltered when its denominator is already within the
    -- limit. `(22, 7, 7)` sits exactly on the boundary and takes it; `(22, 7, 6)` is one below
    -- and runs the loop. Integer targets take the fast path for every limit.
    (4321, 8765, 10000, 4321, 8765),
    (-4321, 8765, 10000, -4321, 8765),
    (22, 7, 1000, 22, 7),
    (22, 7, 7, 22, 7),
    (22, 7, 6, 19, 6),
    (-22, 7, 6, -19, 6),
    (0, 1, 3, 0, 1),
    (7, 1, 5, 7, 1),
    (-7, 1, 5, -7, 1),
    -- Ties at equal denominators, which arise only at a limit of one, for a target midway
    -- between two consecutive integers. The lesser of the two values is returned, which for a
    -- negative target is the one further from zero.
    (1, 2, 1, 0, 1),
    (-1, 2, 1, -1, 1),
    (3, 2, 1, 1, 1),
    (-3, 2, 1, -2, 1),
    (5, 2, 1, 2, 1),
    (-5, 2, 1, -3, 1),
    -- Ties where the denominators differ and settle it on their own. `5/4` is midway between
    -- `1/1` and `3/2`, and `7/4` between `3/2` and `2/1`; the denominator-one candidate wins
    -- both, though it is the lesser value in the first and the greater in the second.
    (5, 4, 2, 1, 1),
    (-5, 4, 2, -1, 1),
    (7, 4, 2, 2, 1),
    (-7, 4, 2, -2, 1),
    -- Cases returning the extended candidate rather than the loop candidate.
    (7, 5, 3, 4, 3),
    (-7, 5, 3, -4, 3),
    -- Cases returning the loop candidate outright.
    (3, 8, 2, 1, 2),
    (17, 12, 5, 7, 5) ]

end
