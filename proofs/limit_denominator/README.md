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

The starting point is the three-argument integer function from the issue, which strips the
`Fraction` wrapping and the fast path away from the standard library version and leaves the
arithmetic:

```python
def limit_denominator(m: int, n: int, l: int) -> tuple[int, int]:
    """
    Given a fraction m/n and a positive integer l, return integers r and s such
    that r/s is the closest fraction to m/n with denominator bounded by l.

    m/n need not be in lowest terms. Raises ValueError if l is less than one, or
    if n is not positive.

    On return, 0 < s <= l and gcd(r, s) = 1.
    """
    if l < 1:
        raise ValueError("max_denominator should be at least 1")
    if n <= 0:
        raise ValueError("denominator should be positive")

    a, b, p, q, r, s = n, m % n, 1, 0, m // n, 1
    while 0 < b and q + a // b * s <= l:
        a, b, p, q, r, s = b, a % b, r, s, p + a // b * r, q + a // b * s
    t, u = p + (l - q) // s * r, q + (l - q) // s * s
    return (r, s) if 2 * b * u <= n else (t, u)
```

This is the issue's listing with two changes. The issue carries a seventh variable `v`,
alternating between `1` and `-1`, which it uses in the statements of the invariants but
which does not affect the result. `v` turns out to equal `p*s - r*q` throughout, so the
proof recovers it from the state rather than tracking it, and the listing drops it. See
[PROOF.md](PROOF.md) for that step.

The second change is the two guards. The issue's listing states a positive `l` and a
positive `n` as preconditions in its docstring and tests neither; here both are enforced,
which is what lets the proof say that *every* input either gets a correct answer or an
exception. Without the `n` check, a negative `n` returns a plausible-looking wrong answer:
`m = 22, n = -7, l = 5` gives `-4/1`, which is out by `6/7`, where the best approximation
to `22/-7` with denominator at most `5` is `-16/5`, out by `2/35`. The message for the `n`
guard is this project's own; the `l` guard's is CPython's, verbatim.

The relationship between this listing and the body of `Fraction.limit_denominator` in
`Lib/fractions.py` is close but not line-for-line: the standard library version operates
on an already-reduced fraction, has a fast path for fractions whose denominator is already
within the limit, uses `while True` with a `break` from the middle rather than a test at
the top, and names its variables `p0, q0, p1, q1` rather than `p, q, r, s`. The issue
discusses those differences. Both listings are translated into Lean and both are proved
correct, against one shared specification — see [Scope](#scope) for where the proof stops.

[PROOF.md](PROOF.md) is the prose companion to the Lean proof: the whole argument in
ordinary mathematical language, with pointers into the source.

## What is proved

The specification is in
[`Specification.lean`](LimitDenominator/Definitions/Specification.lean). It says that a
returned `r / s` is in lowest terms with `0 < s ≤ l`, and that against every candidate
`y / z` with `0 < z ≤ l` it is at least as close to the target, with ties broken towards
the smaller denominator and a tie that survives that towards the lower value:

```lean
def isBestApproximation (m n l r s : Int) : Prop :=
  0 < s ∧ s ≤ l ∧ Int.gcd r s = 1 ∧
  ∀ y z : Int, 0 < z → z ≤ l →
    atLeastAsClose m n r s y z
    ∧ (atLeastAsClose m n y z r s → s ≤ z)
    ∧ (atLeastAsClose m n y z r s → s = z → r ≤ y)
```

All three quantified clauses are promises CPython makes — the first in its documentation, the
other two in the algorithm notes in its source. Candidates are not required to be in lowest
terms, so the result has to beat unreduced competitors too.

### The simplified listing

The theorem, at the bottom of
[`SimplifiedCorrectness.lean`](LimitDenominator/Proofs/SimplifiedCorrectness.lean), is:

```lean
theorem isCorrectLimitDenominator_simplified :
    isCorrectLimitDenominator (fun _ n => 0 < n) limitDenominatorSimplified
```

where `isCorrectLimitDenominator valid f` says that `f` raises `ValueError` with CPython's
message whenever the denominator limit is not positive, and otherwise returns a best
approximation. The `valid` parameter carries the precondition: here, that the target's
denominator is positive.

A target denominator that is not positive is rejected rather than left unspecified:

```lean
theorem limitDenominatorSimplified_raises_of_denominator_nonpos {m n l : Int}
    (hn : n ≤ 0) (hl : 0 < l) :
    raises (limitDenominatorSimplified m n l) (.valueError "denominator should be positive")
```

Python cannot produce such a target — a `Fraction`'s denominator is always positive — so this
is a promise the project invents rather than one it records, which is why the message is not
CPython's. It earns its place by making the behaviour exhaustive:

```lean
theorem limitDenominatorSimplified_total (m n l : Int) :
    raises (limitDenominatorSimplified m n l) (.valueError "max_denominator should be at least 1")
    ∨ raises (limitDenominatorSimplified m n l) (.valueError "denominator should be positive")
    ∨ ∃ r s, returns (limitDenominatorSimplified m n l) (r, s)
        ∧ isBestApproximation m n l r s
```

Every division after the two guards is provably safe — `a // b` is protected by the loop
condition, `(l - q) // s` by `0 < s` — so those two `ValueError`s are the only exceptions
reachable, and there is no input for which the function quietly returns something that is not
the best approximation.

### The standard library listing

The body of `Fraction.limit_denominator` as shipped is translated in
[`LimitDenominatorStdlib.lean`](LimitDenominator/Definitions/LimitDenominatorStdlib.lean) and
proved against the same specification, at the bottom of
[`StdlibCorrectness.lean`](LimitDenominator/Proofs/StdlibCorrectness.lean):

```lean
theorem isCorrectLimitDenominator_stdlib :
    isCorrectLimitDenominator (fun m n => 0 < n ∧ Int.gcd m n = 1) limitDenominatorStdlib
```

Here `valid` carries two conditions rather than one. Being a method, the shipped code reads
its target off a `Fraction`, which keeps its denominator positive and its ratio in lowest
terms. The shipped code tests neither, and neither does the translation.

Those hypotheses are load-bearing, and not only for the tie-break. A target that is not in
lowest terms can drive the loop's `b` to zero, and with no `0 < b` in the shipped loop
condition the next iteration divides by it: `limitDenominatorStdlib 2 4 3` raises
`ZeroDivisionError`, where the simplified listing returns `1/2`. So the shipped listing has
no counterpart to `limitDenominatorSimplified_total` above — outside `valid` there is nothing
to promise. Within it, the argument that the missing test costs nothing is in
[PROOF.md](PROOF.md#what-the-stdlib-listing-adds).

## Scope

What is proved is the arithmetic: both listings, as functions from integers to integers or an
exception. What is not proved is the `Fraction` wrapping that the shipped method puts around
that arithmetic — the `max_denominator=1000000` default, the `Fraction(self)` the fast path
returns, and `Fraction._from_coprime_ints`, CPython's *unchecked* constructor, which the
translation replaces with the numerator/denominator pair itself.

Nor is the invariant a `Fraction` maintains proved here — that is its constructor's job, not
this algorithm's. A positive denominator and a ratio in lowest terms are hypotheses of
`isCorrectLimitDenominator_stdlib`, not conclusions. Bundling them into a Lean type instead
would put a coprimality proof in the definitions layer, the one layer a reader is asked to
read: `_from_coprime_ints` verifies nothing, so a proof field of that shape could only be
filled at the return sites by proving there what this project proves elsewhere. A visible
hypothesis is better than one hidden inside a type.

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
| [`SupportLemmas.lean`](LimitDenominator/Proofs/SupportLemmas.lean) | general `Int` facts the core library lacks |
| [`WhileLoop.lean`](LimitDenominator/Proofs/WhileLoop.lean) | driving a `while` loop with a measure and an invariant, or peeling one iteration, monad-agnostically |
| [`PythonTranslation.lean`](LimitDenominator/Proofs/PythonTranslation.lean) | bridges from `pyFloordiv`, `pyMod` and `<&&>` to plain `Int` |
| [`LoopInvariant.lean`](LimitDenominator/Proofs/LoopInvariant.lean) | the loop invariant, its preservation, and the facts derived from it |
| [`AfterLoop.lean`](LimitDenominator/Proofs/AfterLoop.lean) | the extended candidate, and the `Bracketing` facts everything downstream uses |
| [`Bracket.lean`](LimitDenominator/Proofs/Bracket.lean) | the bracket lemma, and distance bounds for candidates outside it |
| [`TieBreak.lean`](LimitDenominator/Proofs/TieBreak.lean) | comparing the two candidates |
| [`BestApproximation.lean`](LimitDenominator/Proofs/BestApproximation.lean) | the three specification clauses, for whichever candidate is returned and for the fast path |
| [`SimplifiedCorrectness.lean`](LimitDenominator/Proofs/SimplifiedCorrectness.lean) | folding the translation onto the loop and reading the result off |
| [`StdlibCorrectness.lean`](LimitDenominator/Proofs/StdlibCorrectness.lean) | the same for the shipped listing, whose first iteration is peeled off and whose fast path is separate |

Two root files import these: [`LimitDenominator.lean`](LimitDenominator.lean) the
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

An incomplete proof is not the only way a theorem can be hollow: an axiom asserted outright
produces no warning at all. So the build also pins what each correctness theorem depends on,
in [`Tests/Axioms.lean`](LimitDenominator/Tests/Axioms.lean) — `propext`, `Classical.choice`
and `Quot.sound`, which are Lean's own three and nothing else. Any addition fails the build,
so this is checked on every run rather than being something a reader has to think to verify.

## What do I need to trust?

The goal is to convince a reader that the Python listing in the overview is correct. A
successful `lake build` says every proof Lean checked is valid. Joining those two things
up requires confidence in:

- **The faithfulness of the Python-to-Lean translation.** If the Lean function runs a
  different algorithm from the Python listing, its correctness says little about the Python.
  This means reading:
  - the two translations, in
    [`LimitDenominatorSimplified.lean`](LimitDenominator/Definitions/LimitDenominatorSimplified.lean)
    and
    [`LimitDenominatorStdlib.lean`](LimitDenominator/Definitions/LimitDenominatorStdlib.lean),
    the latter of which quotes the shipped Python beside the Lean;
  - the Python primitives — the Lean versions of `//` and `%` — in
    [`PythonPrimitives.lean`](LimitDenominator/Definitions/PythonPrimitives.lean), and
    Python's `and`, which is core's `andM`, under
    [`and` that short-circuits](#and-that-short-circuits);
  - the exception definitions in
    [`Exceptions.lean`](LimitDenominator/Definitions/Exceptions.lean).
- **The statements of correctness** in
  [`Specification.lean`](LimitDenominator/Definitions/Specification.lean), in particular
  `atLeastAsClose`, `isBestApproximation` and `isCorrectLimitDenominator`. A specification
  that is too weak would be easy to satisfy and would prove nothing interesting. One check on
  that is proved rather than argued:
  [`isBestApproximation_unique`](LimitDenominator/Proofs/BestApproximation.lean) shows that
  at most one pair satisfies `isBestApproximation`, so the specification pins the answer down
  completely and cannot be met by some unintended pair as well.
- **That `lake build` really checks the proofs** of the four correctness statements: the
  three at the bottom of
  [`SimplifiedCorrectness.lean`](LimitDenominator/Proofs/SimplifiedCorrectness.lean) —
  `isCorrectLimitDenominator_simplified`,
  `limitDenominatorSimplified_raises_of_denominator_nonpos` and
  `limitDenominatorSimplified_total` — and `isCorrectLimitDenominator_stdlib` at the bottom
  of [`StdlibCorrectness.lean`](LimitDenominator/Proofs/StdlibCorrectness.lean). That they
  are proved rather than asserted does not have to be taken on trust: their axiom sets are
  pinned by the build, as described under [Building](#building).
- **The Lean toolchain**, including its compiler and core library. It is conceivable, if very
  unlikely, that Lean has a bug that lets it accept an invalid proof.

Notably the proofs themselves do *not* need to be trusted. However gnarly they look, if
Lean says they are valid then they are valid. So it is enough to read everything under
[`LimitDenominator/Definitions`](LimitDenominator/Definitions) — the two translations, the
Python primitives, the exceptions and the specification — plus the statements, but not the
proofs, of those four theorems. The proof layer is several times the size of the
definitions, and none of it has to be read.

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
  if n ≤ 0 then
    throw <| .valueError "denominator should be positive"

  let mut (a, b, p, q, r, s) := (n, ← m % n, 1, 0, ← m // n, 1)
  while ← pure (0 < b : Bool) <&&> (do return q + (← a // b) * s ≤ l) do
    (a, b, p, q, r, s) := (b, ← a % b, r, s, p + (← a // b) * r, q + (← a // b) * s)
  let (t, u) := (p + (← (l - q) // s) * r, q + (← (l - q) // s) * s)
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
`Lean.Order.MonadTail` instance — and `Except ε` has one. Strong induction on a measure
turns that single step into termination, which is
[`forIn_loop_invariant`](LimitDenominator/Proofs/WhileLoop.lean). No fuel parameter and no
rewrite into a recursive helper is needed, so the loop in the Lean listing is a plain
`while`.

Python's tuple assignment in the loop body is genuinely simultaneous — the right-hand
side mentions the old `a`, `b`, `p`, `q`, `r` and `s` — and Lean's `let mut (a, b, p, q,
r, s) := …` and six-way reassignment `(a, b, p, q, r, s) := …` translate it directly,
with the same simultaneity.

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
`let mut (a, b, p, q, r, s) := (n, ← m % n, …)`, the subexpression `m % n` has type
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
cases returning each of the two candidates. The simplified listing's adds unreduced targets,
and its integer targets exit the loop immediately with `b = 0`, so the short-circuiting `and`
is what stops the division by zero there. The shipped listing's adds the fast path, on its
boundary and one below.

The exception cases sit beside each listing's other checks rather than in the vectors, which
hold returned values only: both `ValueError`s for the simplified listing, including which
message wins when the limit and the target are both bad, and for the shipped listing the
limit's alone, that being the only exception a valid target can provoke.

**The specification, evaluated.** Expected-value vectors barely exercise a specification
whose substance is a `∀`-quantified optimality condition, so
[`SpecCheck.lean`](LimitDenominator/Tests/SpecCheck.lean) defines a `Bool`-valued bounded
form of `isBestApproximation` and checks it over every target `m / n` with `1 ≤ n ≤ 16`
and `-32 ≤ m ≤ 32` against every limit `1 ≤ l ≤ 12`. The `z` in the
specification are bounded, so they are enumerated; the `y` are not, so for each `z` only
the two integers bracketing `m·z/n` are checked, which suffices for the reason given in
the docstring there.

Both listings are checked that way. The shipped one is checked over the grid's targets that
are in lowest terms, which are the only ones it promises anything about, and over those it is
also checked to agree with the simplified listing outright.

**The axiom sets.** [`Axioms.lean`](LimitDenominator/Tests/Axioms.lean) asserts, for each of
the four correctness theorems, that it depends on `propext`, `Classical.choice` and
`Quot.sound` and nothing else. Unlike the other three this is not an empirical check — it is
a statement about the proofs, and it is what closes the gap `--wfail` leaves, since an
outright `axiom` earns no warning. Each theorem is checked in its own right rather than
leaning on the trichotomy to cover the other two, so reworking one proof cannot quietly
narrow what is checked.

Separately from Lean, the Python listing at the top of this README was
differential-tested against `Fraction.limit_denominator` over 150,696 cases (`n` in
1…39, `m` in −80…80, `l` in 1…24) with no mismatches, asserting `gcd(r, s) = 1` and
`0 < s ≤ l` throughout. `limitDenominatorStdlib` was differential-tested against the same
function in the same way, over 94,207 cases: targets in lowest terms with `1 ≤ n ≤ 40`,
`−80 ≤ m ≤ 80` and `1 ≤ l ≤ 24`, plus this README's examples and a few wide ones, again with
identical output throughout.

[batteries]: https://github.com/leanprover-community/batteries
[do-unchained]: https://lean-lang.org/papers/do.pdf
[elan]: https://github.com/leanprover/elan
[elan-installation]: https://github.com/leanprover/elan?tab=readme-ov-file#installation
[issue]: https://github.com/python/cpython/issues/95723
[limit-denominator]: https://docs.python.org/3/library/fractions.html#fractions.Fraction.limit_denominator
[mathlib]: https://github.com/leanprover-community/mathlib4
