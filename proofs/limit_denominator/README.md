# Formal proof of correctness for Python's `limit_denominator` algorithm

This Lean project provides a formal machine-verifiable proof of correctness of the
algorithm underlying Python's `Fraction.limit_denominator`. It starts with a version of
the algorithm written in Python, translates that into Lean, and then proves the translated
version correct.

## Overview

[`Fraction.limit_denominator`][limit-denominator] finds the closest fraction to a given
one with a bounded denominator:

```pycon
>>> from fractions import Fraction
>>> Fraction('3.141592653589793').limit_denominator(10)
Fraction(22, 7)
>>> Fraction('3.141592653589793').limit_denominator(100)
Fraction(311, 99)
```

Why it works is not obvious. The comments in the CPython source appeal to the theory of
continued fractions — convergents and semiconvergents, best upper and lower
approximations — and the standard references either state the relevant facts without proof
or develop a chapter of theory to reach them. In 2022 the author of that code recorded a
targeted proof, which needs none of that machinery, in
[python/cpython#95723][issue]. This project formalises that proof.

The algorithm this project proves correct is the three-argument integer function from the
issue, which strips the `Fraction` wrapping and the fast path away from the standard
library version and leaves the arithmetic:

```python
def limit_denominator(m: int, n: int, l: int) -> tuple[int, int]:
    """
    Given a fraction m/n and a positive integer l, return integers r and s such
    that r/s is the closest fraction to m/n with denominator bounded by l.

    m/n need not be in lowest terms, but n must be positive.

    On return, 0 < s <= l and gcd(r, s) = 1.
    """
    if l < 1:
        raise ValueError("max_denominator should be at least 1")

    a, b, p, q, r, s = n, m % n, 1, 0, m // n, 1
    while 0 < b and q + a // b * s <= l:
        a, b, p, q, r, s = b, a % b, r, s, p + a // b * r, q + a // b * s
    t, u = p + (l - q) // s * r, q + (l - q) // s * s
    return (r, s) if 2 * b * u <= n else (t, u)
```

This is the issue's listing with one change: the issue carries a seventh variable `v`,
alternating between `1` and `-1`, which it uses in the statements of the invariants but
which does not affect the result. `v` turns out to equal `p*s - r*q` throughout, so the
proof recovers it from the state rather than tracking it, and the listing drops it. See
[PROOF.md](PROOF.md) for that step.

The relationship between this listing and the body of `Fraction.limit_denominator` in
`Lib/fractions.py` is close but not line-for-line: the standard library version operates
on an already-reduced fraction, has a fast path for fractions whose denominator is already
within the limit, uses `while True` with a `break` from the middle rather than a test at
the top, and names its variables `p0, q0, p1, q1` rather than `p, q, r, s`. The issue
discusses those differences. **This project does not yet prove the standard library
version correct** — see [Scope](#scope) below.

[PROOF.md](PROOF.md) is the prose companion to the Lean proof: the whole argument in
ordinary mathematical language, with pointers into the source.

## What is proved

The specification is in
[`Specification.lean`](LimitDenominator/Definitions/Specification.lean). It says that a
returned `r / s` is in lowest terms with `0 < s ≤ l`, and that against every candidate
`y / z` with `0 < z ≤ l` it is at least as close to the target, with ties broken towards
the smaller denominator and any remaining tie towards the smaller fraction:

```lean
def isBestApproximation (m n l r s : Int) : Prop :=
  0 < s ∧ s ≤ l ∧ Int.gcd r s = 1 ∧
  ∀ y z : Int, 0 < z → z ≤ l →
    atLeastAsClose m n r s y z
    ∧ (atLeastAsClose m n y z r s → s ≤ z)
    ∧ (atLeastAsClose m n y z r s → s = z → r ≤ y)
```

All three quantified clauses are promises the CPython documentation and source comments
make. Candidates are not required to be in lowest terms, so the result has to beat
unreduced competitors too.

The theorem, at the bottom of
[`SimplifiedCorrectness.lean`](LimitDenominator/Proofs/SimplifiedCorrectness.lean), is:

```lean
theorem isCorrectLimitDenominator_simplified :
    isCorrectLimitDenominator (fun _ n => 0 < n) limitDenominatorSimplified
```

where `isCorrectLimitDenominator valid f` says that `f` raises `ValueError` with CPython's
message whenever the denominator limit is below one, and otherwise returns a best
approximation. The `valid` parameter carries the precondition: here, that the target's
denominator is positive.

Behaviour for `n ≤ 0` is deliberately left unspecified rather than left out by oversight.
Python cannot produce such a target — a `Fraction`'s denominator is always positive — so
specifying it would be inventing a promise rather than recording one. In the Lean
translation such a call raises `ZeroDivisionError` from the `m % n` on the first line, and
there is a test to that effect, but the theorem says nothing about it.

## Scope

This project currently covers the simplified integer listing above. Extending it to the
body of `Fraction.limit_denominator` as shipped is future work: the specification and the
mathematics are already stated in the generality needed for both, and what remains is a
second translation plus the loop mechanics for `while True` with a mid-loop `break`, and
the argument (issue § "Optimization") that the `0 < b` test is unnecessary once the fast
path guarantees `l < n` for a reduced target.

## Project structure

The Lean source is organised into three subdirectories of
[`LimitDenominator`](LimitDenominator):

- [`LimitDenominator/Definitions`](LimitDenominator/Definitions) holds the Lean
  translation of the algorithm, the supporting definitions of Python primitives and
  exceptions, and the *statements* (but not proofs) of what correctness means.
- [`LimitDenominator/Proofs`](LimitDenominator/Proofs) holds the correctness theorem and
  its supporting lemmas.
- [`LimitDenominator/Tests`](LimitDenominator/Tests) holds `#guard`-based checks: the
  Python primitives, expected-value vectors, and an executable form of the specification
  evaluated over a grid of targets.

The proof layer separates the *mechanics* — unravelling the `do` block, bridging Python's
division to Euclidean division, driving the loop — from the *mathematics*, and the file
names follow that split:

| File | Role |
| --- | --- |
| [`SupportLemmas.lean`](LimitDenominator/Proofs/SupportLemmas.lean) | general `Int` facts the core library lacks |
| [`WhileLoop.lean`](LimitDenominator/Proofs/WhileLoop.lean) | driving a `while` loop with a measure and an invariant, monad-agnostically |
| [`PythonTranslation.lean`](LimitDenominator/Proofs/PythonTranslation.lean) | bridges from `pyFloordiv`, `pyMod`, `pyAnd` to plain `Int` |
| [`LoopInvariant.lean`](LimitDenominator/Proofs/LoopInvariant.lean) | the loop invariant, its preservation, and the residuals |
| [`AfterLoop.lean`](LimitDenominator/Proofs/AfterLoop.lean) | the extended candidate, and the `Bracketing` facts everything downstream uses |
| [`Bracket.lean`](LimitDenominator/Proofs/Bracket.lean) | the bracket lemma, and distance bounds for candidates outside it |
| [`TieBreak.lean`](LimitDenominator/Proofs/TieBreak.lean) | comparing the two candidates |
| [`BestApproximation.lean`](LimitDenominator/Proofs/BestApproximation.lean) | the three specification clauses, for whichever candidate is returned |
| [`SimplifiedCorrectness.lean`](LimitDenominator/Proofs/SimplifiedCorrectness.lean) | folding the translation onto the loop and reading the result off |

Three root files import these: [`LimitDenominator.lean`](LimitDenominator.lean) the
definitions and proofs, and
[`LimitDenominatorTests.lean`](LimitDenominatorTests.lean) the tests.

The project does not depend on [Mathlib][mathlib]: its proofs, definitions and tests use
only Lean's core library. The sole external dependency is [Batteries][batteries], and that
only to provide the linter (`lake lint`) — no Batteries code is used in the proofs.

## Validating the proof

### Prerequisites

Install [elan][elan] (the Lean version manager), following the [installation
instructions][elan-installation] in that project's README. Check that `elan` and `lake`
are on your `PATH`.

### Building

All the commands are run through Lean's build tool, `lake`, from the directory containing
this README. The first `lake` invocation downloads the toolchain version pinned in
[`lean-toolchain`](lean-toolchain).

```
lake build            # build the project - definitions, proofs and tests
lake build --wfail    # build, failing on warnings too (matches CI)
lake lint             # check for style issues
```

A successful `lake build` (exit code 0, no error messages) means Lean mechanically checked
every step of the proofs. The stronger `lake build --wfail` turns warnings into errors;
notably, plain `lake build` still passes, with warnings, in the presence of an incomplete
proof marked `sorry`, whereas `lake build --wfail` fails.

## What do I need to trust?

The goal is to convince a reader that the Python listing in the overview is correct. A
successful `lake build` says every proof Lean checked is valid. Joining those two things
up requires confidence in:

- **The faithfulness of the Python-to-Lean translation.** If the Lean function runs a
  different algorithm from the Python listing, its correctness says little about the
  Python. This means reading:
  - the translation itself, in
    [`LimitDenominatorSimplified.lean`](LimitDenominator/Definitions/LimitDenominatorSimplified.lean);
  - the Python primitives — the Lean versions of `//`, `%` and `and` — in
    [`PythonPrimitives.lean`](LimitDenominator/Definitions/PythonPrimitives.lean);
  - the exception definitions in
    [`Exceptions.lean`](LimitDenominator/Definitions/Exceptions.lean).
- **The statements of correctness** in
  [`Specification.lean`](LimitDenominator/Definitions/Specification.lean), in particular
  `atLeastAsClose`, `isBestApproximation` and `isCorrectLimitDenominator`. A specification
  that is too weak would be easy to satisfy and would prove nothing interesting. One check
  on that is proved rather than argued:
  [`isBestApproximation_unique`](LimitDenominator/Proofs/BestApproximation.lean) shows that
  at most one pair satisfies `isBestApproximation`, so the specification pins the answer
  down completely and cannot be met by some unintended pair as well.
- **That `lake build` really checks the proof** of the correctness statement, which is the
  one-line `theorem isCorrectLimitDenominator_simplified : ...` near the bottom of
  [`SimplifiedCorrectness.lean`](LimitDenominator/Proofs/SimplifiedCorrectness.lean).
- **The Lean toolchain**, including its compiler and core library. It is conceivable, if
  very unlikely, that Lean has a bug that lets it accept an invalid proof.

Notably the proofs themselves do *not* need to be trusted. However gnarly they look, if
Lean says they are valid then they are valid. So it is enough to read everything under
[`LimitDenominator/Definitions`](LimitDenominator/Definitions) — 170 lines including
docstrings, comments and blank lines — plus the one-line statement, but not the proof, of
`isCorrectLimitDenominator_simplified`.

There are also empirical checks under
[`LimitDenominator/Tests`](LimitDenominator/Tests). These are not formal proofs, but they
provide readable evidence, and one of them evaluates the specification itself rather than
comparing against expected values — see [Testing](#testing).

## Notes on the Python-to-Lean translation

Fidelity is the goal: a reader should be able to see that the Lean and the Python are the
same algorithm. Lean 4's support for imperative-looking code — `do` notation, mutable
variables, `while` loops, exceptions — makes a close translation possible. Here it is:

```lean
def limitDenominatorSimplified (m n l : Int) : PyExcept (Int × Int) := do
  if l < 1 then
    throw <| .valueError "max_denominator should be at least 1"

  let mut (a, b, p, q, r, s) := (n, ← m % n, 1, 0, ← m // n, 1)
  while ← pyAnd (0 < b) (do return q + (← a // b) * s ≤ l) do
    (a, b, p, q, r, s) := (b, ← a % b, r, s, p + (← a // b) * r, q + (← a // b) * s)
  let (t, u) := (p + (← (l - q) // s) * r, q + (← (l - q) // s) * s)
  return if 2 * b * u ≤ n then (r, s) else (t, u)
```

Line for line against the Python, with three things worth explaining.

### Division that raises

Python's `//` and `%` on two `int`s differ from Lean's `/` and `%` on two `Int`s in two
ways: for negative divisors Lean's operators round towards zero rather than down, and on a
zero divisor Lean returns `0` where Python raises `ZeroDivisionError`.

Rather than argue that neither difference matters here, the translation models Python's
semantics directly, returning either a value or an exception:

```lean
def pyFloordiv (a b : Int) : PyExcept Int := do
  if b = 0 then throw <| .zeroDivisionError "division by zero"
  return Int.fdiv a b

def pyMod (a b : Int) : PyExcept Int := do
  if b = 0 then throw <| .zeroDivisionError "division by zero"
  return Int.fmod a b
```

`Int.fdiv` and `Int.fmod` are Lean's floor-rounding division and modulus, which match
Python's `//` and `%` for divisors of either sign; the guard supplies the exception. Both
are then given infix notation at Python's precedence, so the translation can write `a // b`
and `a % b`.

This matters more than it might seem: the loop condition `0 < b and q + a // b * s <= l`
divides by `b`, and on the final iteration `b` can be zero. Getting the exception
behaviour right is what makes the next point necessary.

### `and` that short-circuits

Python's `and` evaluates its right operand only if its left one is truthy. That is
load-bearing here: with `b = 0`, `q + a // b * s` would raise, and it is only the `0 < b`
on the left that stops it.

Lean's `&&` short-circuits too, but the translation cannot use it. Lean's `do` elaborator
hoists a nested action `←` out of the surrounding expression and evaluates it *before* the
expression, so `0 < b && (q + (← a // b) * s ≤ l)` performs the division first — raising
exactly where Python exits cleanly. Instead, the delayed operand is passed as a `do` block
to a named function:

```lean
def pyAnd (x : Bool) (y : PyExcept Bool) : PyExcept Bool := do
  if x then y else return false
```

used as `pyAnd (0 < b) (do return q + (← a // b) * s ≤ l)`. Notation would be neater, but
no notation can work: the `do` elaborator harvests `←` from the *unexpanded* syntax tree,
so a macro that wraps its operand in `do` arrives too late. Worse, such a macro compiles
and silently gets the semantics wrong, so `pyAnd` is applied by name, with the delay
visible at the call site.

There is a test in
[`Tests/PythonPrimitives.lean`](LimitDenominator/Tests/PythonPrimitives.lean) that pins
the short-circuiting down, by giving `pyAnd` a right operand that divides by zero.

### `while` loops and simultaneous assignment

Lean's `while` elaborates to `Lean.Loop.forIn`, built on a `partial def`, so it has no
equation lemmas of its own. What it does have, from Lean 4.32, is
`Lean.Loop.forIn_eq_of_monadTail`, which unfolds it one step in any monad with a
`Lean.Order.MonadTail` instance — and `Except ε` has one. Strong induction on a measure
turns that single step into termination, which is
[`forIn_loop_invariant`](LimitDenominator/Proofs/WhileLoop.lean). No fuel parameter and no
rewrite into a recursive helper is needed, so the loop in the Lean listing is a plain
`while`.

Python's tuple assignment in the loop body is genuinely simultaneous — the right-hand
side mentions the old `a`, `b`, `p`, `q`, `r` and `s` — and Lean's `let mut (a, b, p, q,
r, s) := …` and six-way reassignment `(a, b, p, q, r, s) := …` translate it directly,
with the same simultaneity.

### Reading `←`

For readers new to Lean's `do` notation: `←` unwraps a computation that might raise. In
`let mut (a, b, p, q, r, s) := (n, ← m % n, …)`, the subexpression `m % n` has type
`PyExcept Int`, and `← m % n` is the `Int` inside it, with any exception propagated out of
the whole `do` block automatically. So each `←` marks a place where the Python could raise
`ZeroDivisionError`. This use inside a larger expression is called a *nested action*; see
[*'do' Unchained*][do-unchained] by Ullrich and de Moura for the details.

## Testing

Two kinds of check live under [`LimitDenominator/Tests`](LimitDenominator/Tests), both run
as part of `lake build`.

**Expected values.** [`Vectors.lean`](LimitDenominator/Tests/Vectors.lean) holds
`(m, n, l, r, s)` tuples, every one of them checked against
`Fraction.limit_denominator` in CPython 3.14. They cover the documentation's examples,
unreduced targets, integer targets (which exit the loop immediately with `b = 0`, so the
short-circuiting `and` is what stops the division by zero), negative targets, halfway ties
at a limit of one and at larger limits, cases returning each of the two candidates, and
the `ValueError`.

**The specification, evaluated.** Expected-value vectors barely exercise a specification
whose substance is a `∀`-quantified optimality condition, so
[`SpecCheck.lean`](LimitDenominator/Tests/SpecCheck.lean) defines a `Bool`-valued bounded
form of `isBestApproximation` and checks it over every target `m / n` with `1 ≤ n ≤ 16`
and `-32 ≤ m ≤ 32` against every limit `1 ≤ l ≤ 12` — 12,480 cases. The `z` in the
specification are bounded, so they are enumerated; the `y` are not, so for each `z` only
the two integers bracketing `m·z/n` are checked, which suffices for the reason given in
the docstring there.

Separately from Lean, the Python listing at the top of this README was
differential-tested against `Fraction.limit_denominator` over 150,696 cases (`n` in
1…39, `m` in −80…80, `l` in 1…24) with no mismatches, asserting `gcd(r, s) = 1` and
`0 < s ≤ l` throughout.

[batteries]: https://github.com/leanprover-community/batteries
[do-unchained]: https://lean-lang.org/papers/do.pdf
[elan]: https://github.com/leanprover/elan
[elan-installation]: https://github.com/leanprover/elan?tab=readme-ov-file#installation
[issue]: https://github.com/python/cpython/issues/95723
[limit-denominator]: https://docs.python.org/3/library/fractions.html#fractions.Fraction.limit_denominator
[mathlib]: https://github.com/leanprover-community/mathlib4
