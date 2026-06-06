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

**Guard**:
The boolean test controlling whether the loop body runs again (Python's
`while <guard>:`). For isqrt, `s > 0`.
_Avoid_: termination condition, predicate, loop condition

**Body**:
The function representing one execution of the loop body — the effect on the
loop state of running the suite once. Mirrors part (c) of the design.
_Avoid_: step, update function, state updater, iteration

**Measure**:
The ℕ-valued function of the loop state that strictly decreases on every
iteration, witnessing termination. The chosen form of evidence (d). For isqrt
the measure is essentially `s`.
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
case plus a body-preservation step. Combined with the return subtype's `¬ guard`
to give the loop postcondition.
_Avoid_: invariant (unqualified)

**pyWhile**:
The generic Lean combinator (in `Isqrt/While.lean`) that represents a simple
Python `while` loop: it takes a guard, a body, a measure, and a measure-decrease
proof, and returns `{ s : σ // ¬ guard s }`. The `py` prefix marks it, like
`pyFloordiv` et al., as a faithful translation of a Python construct.
_Avoid_: while, whileLoop, loop
