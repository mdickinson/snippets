# Formal proof of correctness for Python's `limit_denominator` algorithm

This Lean project provides a formal machine-verifiable proof of correctness of the
algorithm underlying Python's `Fraction.limit_denominator`. It starts with a version of
the algorithm written in Python, translates that into Lean, and then proves the
translated version correct.

## Overview

The [`Fraction.limit_denominator`][limit-denominator] method finds a best-possible
approximation to a target fraction, under the constraint that the approximation must be
a fraction whose denominator is no larger than a given bound:

```pycon
>>> from fractions import Fraction
>>> Fraction('3.141592653589793')
Fraction(3141592653589793, 1000000000000000)
>>> Fraction('3.141592653589793').limit_denominator(10)
Fraction(22, 7)
>>> Fraction('3.141592653589793').limit_denominator(100)
Fraction(311, 99)
```

The [implementation][cpython-source] of the method is short — around 20 lines of Python
— but its correctness is not immediately obvious. The comments in the source appeal to
the theory of continued fractions. References that are readily available either
state the relevant facts without proof or develop a chapter of theory to reach them.
However, it is possible to give a short, targeted proof of correctness from first
principles that does not require any explicit mention of continued fractions. An
informal proof along these lines is recorded in [python/cpython#95723][issue]. This
project provides a formal, machine-checkable proof.

## What is proved

The project defines two functions in Lean: `limitDenominatorStdlib` and
`limitDenominatorSimplified`. The first is an almost line-for-line translation of the
`Fraction.limit_denominator` Python source into the Lean programming language. The
second is a similarly faithful line-by-line translation of the simplified listing in
the issue. Those two translations can be found at
[`LimitDenominatorStdlib.lean`](LimitDenominator/Definitions/LimitDenominatorStdlib.lean)
and
[`LimitDenominatorSimplified.lean`](LimitDenominator/Definitions/LimitDenominatorSimplified.lean),
respectively.

Both Lean functions are then proved correct. Saying exactly what correctness means
needs a definition first. Given a denominator limit $\ell$, say that a fraction $r / s$
is a **best** approximation to a target fraction $m / n$ if:

- $0 < s \le \ell$
- for any fraction $y / z$ with $0 < z \le \ell$, reduced or not, either
  - $y / z$ is further away from $m / n$ than $r / s$ is, or
  - $y / z$ and $r / s$ are equidistant from $m / n$, and $s \le z$

An implementation of the algorithm is then **correct** if:

- for a nonpositive limit, a `ValueError` exception is raised with CPython's message
- for a positive limit and a _valid_ target fraction, the returned approximation
  fraction is a best approximation

The meaning of "valid" is different for the two listings. The project does not define
a `Fraction` type in Lean, so both translations take a pair of integers (numerator and
denominator) in place of the target `Fraction`. For `limitDenominatorStdlib`, a valid
target has relatively prime numerator and denominator, and a positive denominator. For
`limitDenominatorSimplified` coprimality is not needed for correctness, so a valid
target is any with a positive denominator. The two conditions are `isValidStdlib` and
`isValidSimplified` in
[`Specification.lean`](LimitDenominator/Definitions/Specification.lean), alongside the
definitions of best approximation and of correctness.

The two correctness theorems are `isCorrectLimitDenominator_stdlib` and
`isCorrectLimitDenominator_simplified`, and those theorems and their proofs can be found
in [`StdlibCorrectness`](LimitDenominator/Proofs/StdlibCorrectness.lean) and
[`SimplifiedCorrectness`](LimitDenominator/Proofs/SimplifiedCorrectness.lean)
respectively.

What is proved correct is the arithmetic. The `Fraction` wrapping that the shipped
method puts around it is not: the default value of `max_denominator`, the
`Fraction(self)` that the fast path returns, and `Fraction._from_coprime_ints`, which
the translation replaces with the numerator/denominator pair itself.

## What's in the project

The main goal of the project is to provide the translations of the two versions of the
algorithm into Lean and correctness proofs for those two translations. The project
contains some other bits and pieces, described below.

### Additional theorems

This project proves some additional facts beyond the above correctness, namely:

- that except in the case when $\ell = 1$ and $m / n$ is halfway between two consecutive
  integers (the **ambiguous case**), there is a unique best approximation to $m / n$
  with denominator bounded by $\ell$
- that in the ambiguous case, there are _two_ best approximations to choose from, namely
  the two integers neighboring $m/n$
- that in the ambiguous case, both versions of the algorithm choose to return the floor
  of $m / n$
- that the returned fraction is always in lowest terms
- that the two implementations agree on every target valid for the standard library
  version

### Prose proof

[PROOF.md](PROOF.md) is the prose companion to the Lean proof: the whole argument in
ordinary mathematical language, with pointers into the source.

### Lean executable

The Lean translation can be run as well as proved, and the project builds a small
command-line executable around the simplified listing — see
[Running the algorithm](#running-the-algorithm).

### Tests

The project has a suite of executable tests, run as part of the build, checking the
translations against CPython's answers and evaluating the specification itself over a
grid of targets — see [Testing](#testing).

## Project structure

The Lean source is organised into three subdirectories of
[`LimitDenominator`](LimitDenominator):

- [`LimitDenominator/Definitions`](LimitDenominator/Definitions) holds the two Lean
  translations of the algorithm, the supporting definitions of Python primitives and
  exceptions, and the *statements* (but not proofs) of what correctness means.
- [`LimitDenominator/Proofs`](LimitDenominator/Proofs) holds the correctness theorems and
  their supporting lemmas.
- [`LimitDenominator/Tests`](LimitDenominator/Tests) holds the build-time checks:
  `#guard`-based checks of the Python primitives, expected-value vectors, an executable form
  of the specification evaluated over a grid of targets, and the pinned axiom sets of the
  correctness theorems.

The proof layer separates the *mechanics* — unravelling the `do` block, bridging Python's
division to Euclidean division, driving the loop — from the *mathematics*, and the file
names follow that split:

| File | Role |
| --- | --- |
| [`IntLemmas.lean`](LimitDenominator/Proofs/IntLemmas.lean) | general `Int` facts the core library lacks |
| [`WhileLoop.lean`](LimitDenominator/Proofs/WhileLoop.lean) | peeling one iteration off a `while` loop, or stopping it, monad-agnostically |
| [`PythonTranslation.lean`](LimitDenominator/Proofs/PythonTranslation.lean) | bridges from `pyFloordiv`, `pyMod` and `<&&>` to plain `Int` |
| [`Arguments.lean`](LimitDenominator/Proofs/Arguments.lean) | the arguments to the algorithm |
| [`Candidate.lean`](LimitDenominator/Proofs/Candidate.lean) | candidate solutions, and when one is better than another or best |
| [`Algorithm.lean`](LimitDenominator/Proofs/Algorithm.lean) | the algorithm as the proof layer computes it: the loop state, running the loop, the state on exit with its two candidates, and the return value |
| [`BaseAnalysis.lean`](LimitDenominator/Proofs/BaseAnalysis.lean) | the bracket on exit, the return value being best, and every best approximation being one of the two endpoints |
| [`Reduced.lean`](LimitDenominator/Proofs/Reduced.lean) | reduced candidates, and every best approximation being reduced |
| [`Optimizations.lean`](LimitDenominator/Proofs/Optimizations.lean) | the shipped listing's two optimizations, valid for a reduced target: the fast path for a trivial input, and the missing `0 < b` test |
| [`Uniqueness.lean`](LimitDenominator/Proofs/Uniqueness.lean) | the ambiguous case, the one place two candidates are best, and the uniqueness of the best approximation everywhere else |
| [`SpecificationBridge.lean`](LimitDenominator/Proofs/SpecificationBridge.lean) | the bridge to the specification: what it does and does not determine |
| [`SimplifiedCorrectness.lean`](LimitDenominator/Proofs/SimplifiedCorrectness.lean) | folding the translation onto the loop and reading the result off |
| [`StdlibCorrectness.lean`](LimitDenominator/Proofs/StdlibCorrectness.lean) | the same for the shipped listing, whose first iteration is peeled off and whose fast path returns what the loop would |
| [`Agreement.lean`](LimitDenominator/Proofs/Agreement.lean) | the two listings agree, from their correctness theorems and what the specification determines |

Two root files import these: [`LimitDenominator.lean`](LimitDenominator.lean) the
definitions and proofs, and
[`LimitDenominatorTests.lean`](LimitDenominatorTests.lean) the tests. Alongside them,
[`Main.lean`](Main.lean) is the source of the command-line executable.

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
lake build                          # definitions, proofs, tests and executable
lake build --wfail                  # build, failing on warnings too (matches CI)
lake exe limit_denominator 22 7 5   # run the executable (should print 16/5)
lake lint                           # check for style issues
```

A successful `lake build` (exit code 0, no error messages) means Lean mechanically checked
every step of the proofs. The stronger `lake build --wfail` turns warnings into errors;
notably, plain `lake build` still passes, with warnings, in the presence of an incomplete
proof marked `sorry`, whereas `lake build --wfail` fails.

An incomplete proof is not the only way a theorem can be hollow: an axiom asserted outright
produces no warning at all. So the build also pins the axioms of each theorem the trust
argument leans on, in [`Tests/Axioms.lean`](LimitDenominator/Tests/Axioms.lean) — `propext`,
`Classical.choice` and `Quot.sound`, which are Lean's own three and nothing else. Any
addition fails the build, so this is checked on every run rather than being something a
reader has to think to verify.

## Running the algorithm

Lean is a programming language as well as a proof assistant, so the translated algorithm
can be run. [`Main.lean`](Main.lean) wraps the simplified listing in a command-line
executable that takes a target `m n l` and prints the closest fraction as `r/s`:

```console
$ lake exe limit_denominator 3141592653589793 1000000000000000 100
311/99
```

A limit below one gets the algorithm's own `ValueError`, on stderr and with a nonzero
exit status:

```console
$ lake exe limit_denominator 22 7 0
ValueError: max_denominator should be at least 1
```

The executable calls `limitDenominatorSimplified` rather than reimplementing it, so what
runs is the proved function; parsing and checking the arguments and formatting the
answer are all that `Main.lean` adds. It also *uses* the proof.
[`limitDenominatorSimplified_total`](LimitDenominator/Proofs/SimplifiedCorrectness.lean)
says that on a positive target denominator the limit's `ValueError` is the only
exception reachable, and that is what lets `Main.lean` dismiss `ZeroDivisionError` as
impossible instead of inventing behaviour for a case that cannot arise. Dismissing it is
a proof obligation, so `lake build` checks it; the proof is then erased from the
compiled binary.

## What do I need to trust?

The goal is to convince a reader that both the simplified Python listing in the issue
and the method implementation in Python's source are correct. A successful `lake build`
says every proof Lean checked is valid. Joining those two things up requires confidence
in:

- **The faithfulness of the Python-to-Lean translation.** If the Lean function runs a
  different algorithm from the Python listing, its correctness says little about the Python.
  This means reading:
  - the two translations, in
    [`LimitDenominatorSimplified.lean`](LimitDenominator/Definitions/LimitDenominatorSimplified.lean)
    and
    [`LimitDenominatorStdlib.lean`](LimitDenominator/Definitions/LimitDenominatorStdlib.lean),
    each of which quotes the Python it translates beside the Lean;
  - the Python primitives — the Lean versions of `//` and `%` — in
    [`PythonPrimitives.lean`](LimitDenominator/Definitions/PythonPrimitives.lean), and
    Python's `and`, which is core's `andM`, under
    [`and` that short-circuits](#and-that-short-circuits);
  - the exception definitions in
    [`Exceptions.lean`](LimitDenominator/Definitions/Exceptions.lean).
- **The statements of correctness** in
  [`Specification.lean`](LimitDenominator/Definitions/Specification.lean), in particular
  `scaledDistance`, `isBetterApproximation`, `isBestApproximation`, `isAmbiguous`,
  `isValidSimplified`, `isValidStdlib` and `isCorrectLimitDenominator`. A specification
  that is too weak would be easy to satisfy and would prove nothing interesting. Three
  checks on that are proved rather than argued, in
  [`SpecificationBridge.lean`](LimitDenominator/Proofs/SpecificationBridge.lean):
  `isBestApproximation_unique_of_not_ambiguous` and
  `isBestApproximation_iff_of_ambiguous` together say exactly how far the specification
  pins the answer down — among all pairs with `0 < z ≤ l`, reduced or not, to one pair
  outside the ambiguous case and to the floor and the floor plus one inside it, so it
  cannot be met by some unintended pair as well; and `isBestApproximation.gcd_eq_one`
  says that whichever pair satisfies it is necessarily reduced, so that promise
  is earned rather than asked for. All three take `0 < n` as a hypothesis, and it is not
  a convenience: with `n = 0` every `r / 1` satisfies the specification, and with
  `n < 0` Lean's `m / n` is not the floor, so the characterisation would name the wrong
  pair. A target denominator that is not positive is outside what the project promises
  anything about, and the hypothesis says so.
- **That `lake build` really checks the proofs** of the statements above: the three at
  the bottom of
  [`SimplifiedCorrectness.lean`](LimitDenominator/Proofs/SimplifiedCorrectness.lean) —
  `isCorrectLimitDenominator_simplified`,
  `limitDenominatorSimplified_returns_floor_of_ambiguous` and
  `limitDenominatorSimplified_total` — the two at the bottom of
  [`StdlibCorrectness.lean`](LimitDenominator/Proofs/StdlibCorrectness.lean) —
  `isCorrectLimitDenominator_stdlib` and
  `limitDenominatorStdlib_returns_floor_of_ambiguous` — the one in
  [`Agreement.lean`](LimitDenominator/Proofs/Agreement.lean) —
  `limitDenominatorStdlib_eq_limitDenominatorSimplified` — and the three about the
  specification itself. That they are proved rather than asserted does not have to be
  taken on trust: their axiom sets are pinned by the build, as described under
  [Building](#building).
- **The Lean toolchain**, including its compiler and core library. It is conceivable, if very
  unlikely, that Lean has a bug that lets it accept an invalid proof.

Notably the proofs themselves do *not* need to be trusted. However gnarly they look, if
Lean says they are valid then they are valid. So it is enough to read everything under
[`LimitDenominator/Definitions`](LimitDenominator/Definitions) — the two translations, the
Python primitives, the exceptions and the specification — plus the statements, but not the
proofs, of those theorems. The proof layer is several times the size of the definitions, and
none of it has to be read.

There are also empirical checks under
[`LimitDenominator/Tests`](LimitDenominator/Tests). These are not formal proofs, but they
provide readable evidence, and one of them evaluates the specification itself rather than
comparing against expected values — see [Testing](#testing).

## Notes on the Python-to-Lean translation

Fidelity is the goal: a reader should be able to see that the Lean and the Python are the
same algorithm. Lean 4's support for imperative-looking code — `do` notation, mutable
variables, `while` loops, exceptions — makes a close translation possible. Here is the
simplified listing:

```lean
def limitDenominatorSimplified (m n l : Int) : PyExcept (Int × Int) := do
  if l < 1 then
    throw <| .valueError "max_denominator should be at least 1"

  let mut (a, b, p, q, r, s, v) := (n, ← m % n, 1, 0, ← m // n, 1, 1)
  while ← pure (0 < b : Bool) <&&> (do return q + (← a // b) * s ≤ l) do
    (a, b, p, q, r, s, v) :=
      (b, ← a % b, r, s, p + (← a // b) * r, q + (← a // b) * s, -v)
  let k ← (l - q) // s
  let (t, u) := (p + k * r, q + k * s)
  return if 2 * b * u ≤ n then (r, s) else (t, u)
```

Line for line against the Python, with four things worth explaining, and a note on reading
`←` for anyone new to Lean's `do` notation.

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

Lean's core library has exactly this operation: `andM`, notated `<&&>`.

```lean
def andM [Monad m] [ToBool β] (x y : m β) : m β := do
  let b ← x
  match toBool b with
  | true => y
  | false => pure b
```

It matches Python closely. The right operand is a *computation*, so it runs only in the
truthy branch; `ToBool` is the truthiness test; and the falsy branch returns the left
operand itself, exactly as `a and b` evaluates to `a` when `a` is falsy. Python is more
liberal in one respect that `limit_denominator` does not need: its two operands may have
different types, where `andM`'s must agree.

On the left, `pure (0 < b : Bool)` wraps the test as a computation of its own. The
ascription is what resolves the proposition `0 < b` to the `Bool` that `andM`'s truthiness
test wants; without it Lean goes looking for a `ToBool Prop` instance and fails.

What `<&&>` cannot do is supply the delay on the right. Lean's `do` elaborator hoists a
nested action `←` out of the surrounding expression and evaluates it *before* the
expression, and it works from the *unexpanded* syntax tree, so no notation can intervene:
`pure (0 < b : Bool) <&&> pure (q + (← a // b) * s ≤ l)` performs the division first,
raising exactly where Python exits cleanly. The right operand has to be written as an
explicit `do` block — and since the wrong spelling compiles and silently misbehaves, the
translation flags that in a comment at the loop. Lean's plain `&&` is no help either: it
does short-circuit, but the `←` is hoisted out before it is ever applied.

There is a test in
[`Tests/PythonPrimitives.lean`](LimitDenominator/Tests/PythonPrimitives.lean) that pins
the short-circuiting down, by giving `<&&>` a right operand that divides by zero.

### `while` loops and simultaneous assignment

Lean's `while` elaborates to `Lean.Loop.forIn`, built on a `partial def`, so it has no
equation lemmas of its own. What it does have, from Lean 4.32, is
`Lean.Loop.forIn_eq_of_monadTail`, which unfolds it one step in any monad with a
`Lean.Order.MonadTail` instance — and `Except ε` has one. That single step is the whole
of [`WhileLoop.lean`](LimitDenominator/Proofs/WhileLoop.lean): one lemma peels an
iteration off the front of the loop, the other stops it. Termination comes from the
proof layer's own model of the loop, `runLoop` in
[`Algorithm.lean`](LimitDenominator/Proofs/Algorithm.lean), a recursive function on a
state that carries the invariants with it; the correctness proof identifies the `do`
block's loop with `runLoop` one iteration at a time, by induction on `runLoop`. No fuel
parameter and no rewrite of the listing into a recursive helper is needed, so the loop
in the Lean listing is a plain `while`.

Python's tuple assignment in the loop body is genuinely simultaneous — the right-hand
side mentions the old `a`, `b`, `p`, `q`, `r`, `s` and `v` — and Lean's
`let mut (a, b, p, q, r, s, v) := …` and seven-way reassignment
`(a, b, p, q, r, s, v) := …` translate it directly, with the same simultaneity.

### `while True` with a `break`

The shipped listing loops the other way round, with `while True` and a `break` from the
middle. In Lean that is `repeat`:

```lean
  repeat
    let a ← n // d
    let q2 := q0 + a * q1
    if q2 > maxDenominator then
      break
    (p0, q0, p1, q1) := (p1, q1, p0 + a * p1, q2)
    (n, d) := (d, n - a * d)
```

`repeat body` is `for _ in Loop.mk do body`, so it elaborates to the same `Lean.Loop.forIn`
that a `while` does and the same loop lemmas apply; the `break` is a `ForInStep.done`
carrying the state out. `while true do` would also run correctly, but `while c do body` is a
macro for `repeat if c then body else break`, so that spelling puts a test in the elaborated
term that the Python does not have.

That translation keeps the shipped variable names, `n` and `d` for the running target among
them — so in that one listing `n` is a numerator, where everywhere else in this project it is
the target's denominator. The Python is quoted beside the Lean in the module docstring for
reading them against each other, and the proof layer renames the state back.

### Reading `←`

For readers new to Lean's `do` notation: `←` unwraps a computation that might raise. In
`let mut (a, b, p, q, r, s, v) := (n, ← m % n, …)`, the subexpression `m % n` has type
`PyExcept Int`, and `← m % n` is the `Int` inside it, with any exception propagated out of
the whole `do` block automatically. So each `←` marks a place where the Python could raise
`ZeroDivisionError`. This use inside a larger expression is called a *nested action*; see
[*'do' Unchained*][do-unchained] by Ullrich and de Moura for the details.

## Testing

Four kinds of check live under [`LimitDenominator/Tests`](LimitDenominator/Tests), all run
as part of `lake build`.

**The Python primitives.**
[`PythonPrimitives.lean`](LimitDenominator/Tests/PythonPrimitives.lean) checks `pyFloordiv`
and `pyMod` against CPython over all four sign combinations, a zero numerator and a zero
divisor, that the `//` and `%` notation agrees with the primitives it abbreviates, and that
`<&&>` short-circuits — a falsy left operand leaves a division by zero on the right unrun,
while a truthy one raises.

**Expected values.** [`Vectors.lean`](LimitDenominator/Tests/Vectors.lean) holds
`(m, n, l, r, s)` tuples, one list per listing, every one of them checked against
`Fraction.limit_denominator` in CPython 3.14. Both lists cover the documentation's examples,
integer targets, negative targets, halfway ties at a limit of one and at larger limits, and
cases returning each of the two candidates. The simplified listing's adds reducible targets,
and its integer targets exit the loop immediately with `b = 0`, so the short-circuiting `and`
is what stops the division by zero there. The shipped listing's adds the fast path, on its
boundary and one below.

The exception cases sit beside each listing's other checks rather than in the vectors,
which hold returned values only: the limit's `ValueError`, for each listing, that being
the only exception a valid target can provoke.

**The specification, evaluated.** Expected-value vectors barely exercise a specification
whose substance is a `∀`-quantified optimality condition, so
[`SpecificationCheck.lean`](LimitDenominator/Tests/SpecificationCheck.lean) defines a
`Bool`-valued bounded form of `isBestApproximation` and checks it over every target
`m / n` with `1 ≤ n ≤ 16` and `-32 ≤ m ≤ 32` against every limit `1 ≤ l ≤ 12`. The `z`
in the specification are bounded, so they are enumerated; the `y` are not, so for each
`z` only the two integers bracketing `m·z/n` are checked, which suffices for the reason
given in the docstring there. Two conjuncts go beyond the specification, deliberately:
that the pair returned is reduced, and that in the ambiguous case it is the floor — the
executable counterparts of `isBestApproximation.gcd_eq_one` and of the two
`returns_floor_of_ambiguous` theorems.

Both listings are checked that way. The shipped one is checked over the grid's reduced
targets, which are the only ones it promises anything about, and over those it is
also checked to agree with the simplified listing outright, the executable counterpart
of `limitDenominatorStdlib_eq_limitDenominatorSimplified`.

**The axiom sets.** [`Axioms.lean`](LimitDenominator/Tests/Axioms.lean) asserts, for
each theorem named under [What do I need to trust?](#what-do-i-need-to-trust), that it
depends on `propext`, `Classical.choice` and `Quot.sound` and nothing else. Unlike the
other three this is not an empirical check — it is a statement about the proofs, and it
is what closes the gap `--wfail` leaves, since an outright `axiom` earns no warning.
Each theorem is checked in its own right rather than leaning on the trichotomy to cover
the other two, so reworking one proof cannot quietly narrow what is checked.

Separately from Lean, the simplified Python listing, as quoted in
[`LimitDenominatorSimplified.lean`](LimitDenominator/Definitions/LimitDenominatorSimplified.lean),
was differential-tested against `Fraction.limit_denominator` over 150,696 cases (`n` in
1…39, `m` in −80…80, `l` in 1…24) with no mismatches, asserting `gcd(r, s) = 1` and
`0 < s ≤ l` throughout. `limitDenominatorStdlib` was differential-tested against the same
function in the same way, over 94,207 cases: reduced targets with `1 ≤ n ≤ 40`,
`−80 ≤ m ≤ 80` and `1 ≤ l ≤ 24`, plus this README's examples and a few wide ones, again with
identical output throughout.

[batteries]: https://github.com/leanprover-community/batteries
[cpython-source]: https://github.com/python/cpython/blob/d220409a13b77de7a6c30abe16ea90db01528edc/Lib/fractions.py#L384-L439
[do-unchained]: https://lean-lang.org/papers/do.pdf
[elan]: https://github.com/leanprover/elan
[elan-installation]: https://github.com/leanprover/elan?tab=readme-ov-file#installation
[issue]: https://github.com/python/cpython/issues/95723
[limit-denominator]: https://docs.python.org/3/library/fractions.html#fractions.Fraction.limit_denominator
[mathlib]: https://github.com/leanprover-community/mathlib4
