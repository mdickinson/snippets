# isqrt_lean4 — `while` loop translation

Glossary for the in-progress work on faithfully representing a simple Python
`while` loop in Lean 4, en route to verifying the *iterative* form of the
integer square root algorithm. "Simple" = no `else` clause, no `break`/
`continue`, no exceptions raised by the loop machinery itself.

This glossary is scoped to the `while`-translation subproblem. The terminology
for the already-finished recursive proof lives in `README.md` and `PLAN.md`.

## Language

**Loop state**:
The bundle of values that the loop mutates across iterations (for isqrt: `s`,
`d`, `a`). The Lean `while` combinator is generic over its type `σ`.
_Avoid_: context, environment, accumulator

**Condition**:
The boolean test controlling whether the loop body runs again (Python's
`while <condition>:`). For isqrt, `s >= 0`. The `pyWhile` argument is named
`condition` — the most Python-idiomatic choice, despite overlapping in wording
with the unrelated `hasSizeCondition` of the recursive proof.
_Avoid_: guard, termination condition, predicate

**Body**:
The function representing one execution of the loop body — the effect on the
loop state of running the suite once. Mirrors part (c) of the design.
_Avoid_: step, update function, state updater, iteration

**Measure**:
The function of the loop state, into some well-founded-ordered type `α`
(`[WellFoundedRelation α]`), that strictly decreases on every iteration,
witnessing termination. The chosen form of evidence (d). `α` is usually `ℕ` (so
the decrease is just `<`); for isqrt the measure is `(s + 1).toNat` (into `ℕ`;
the `+1` keeps it strictly decreasing through the final `s = 0 → −1` step). A
non-`ℕ` `α` (e.g. `ℕ ×ₗ ℕ`, lexicographic) is available when no single `ℕ` fits.
_Avoid_: variant, rank, ranking function, fuel, bound

**Well-definedness invariant**:
The *minimal* property bundled into the state type `σ` (a subtype) — exactly
enough for the body to typecheck by discharging its py-op preconditions
(`a > 0`, shift-nonnegativity, …). Established at the seed state and
re-established by the body each step. Deliberately kept small; richer properties
are not put here.
_Avoid_: precondition, contract, invariant (unqualified)

**Loop property**:
A richer invariant (notably the near-√ property) proved *after the fact* about
`pyWhile`'s result via the `pyWhile_invariant` companion lemma — the standard
partial-correctness while rule. Not bundled into `σ`; established from a seed
case plus a body-preservation step. Combined with the return subtype's
`¬ condition` to give the loop postcondition. For the iterative isqrt it is
`isNearSqrt a (n at depth d)` and nothing more — the size condition is kept out.
_Avoid_: invariant (unqualified)

**n at depth d**:
The value `n` takes in the recursion subproblem whose `c`-argument is `d`:
`⌊n / 4^(c−d)⌋ = n >> 2(c−d)` (written `N_d`). The iterative loop climbs `d` up
the chain `c >> j` that the recursion descends; at each step `a` is tracked as a
near square root of `N_d`. At loop exit `d = c`, so `N_c = n`. The pair `(d, N_d)`
is a size-condition pair of the recursive proof.
_Avoid_: residual, remainder, subproblem input

**pyWhile**:
The generic Lean combinator (in `Isqrt/While.lean`) that represents a simple
Python `while` loop: it takes the initial state, a condition, a body, a measure,
and a measure-decrease proof (the non-evidence arguments ordered to mirror
Python's `while` loop: initial state, then condition, then body), and returns
`{ s : σ // ¬ condition s }`. The `py` prefix marks it, like `pyFloordiv` et
al., as a faithful translation of a Python construct.
_Avoid_: while, whileLoop, loop
