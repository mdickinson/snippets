# Correctness proof for CPython's `math.integer.isqrt`

This repository provides a formal machine-verifiable proof of correctness of the
algorithm underlying the CPython implementation of Python's `math.integer.isqrt`
function. It starts with a version of the algorithm written in Python, translates that
into Lean, and then proves correctness of the translated version.

## Overview

Python's `math.integer.isqrt` standard library function (`math.isqrt` prior to Python
3.15) computes the integer square root of a nonnegative integer `n`: the unique
integer `a` satisfying `a * a <= n < (a + 1) * (a + 1)`.

The function is implemented in C, but the CPython source code describes an equivalent Python
implementation, which the C implementation follows closely. Here's that implementation.
(Sources: [original
commit](https://github.com/python/cpython/blob/73934b9da07daefb203e7d26089e7486a1ce4fdf/Modules/mathmodule.c#L1515-L1535)
for Python 3.8; [current home in
math.integer](https://github.com/python/cpython/blob/v3.15.0b1/Modules/mathintegermodule.c#L191-L211).)

```python
def isqrt(n):
    """
    Return the integer part of the square root of the input.
    """
    n = operator.index(n)

    if n < 0:
        raise ValueError("isqrt() argument must be nonnegative")
    if n == 0:
        return 0

    c = (n.bit_length() - 1) // 2
    a = 1
    d = 0
    for s in reversed(range(c.bit_length())):
        # Loop invariant: (a-1)**2 < (n >> 2*(c - d)) < (a+1)**2
        e = d
        d = c >> s
        a = (a << d - e - 1) + (n >> 2*c - e - d + 1) // a

    return a - (a*a > n)
```

Despite its simplicity, the algorithm is unpublished and novel and in places quite
delicate, so some skepticism about its correctness is justified. This repository
provides a direct, faithful line-by-line translation of the above algorithm into the
Lean programming language, along with a formal machine-checkable proof of correctness of
that translation.

While the iterative version above is what's implemented in CPython, the algorithm as
originally derived was recursive, and is conceptually clearer when presented that way.
This repository also contains a definition and proof of correctness for the recursive
spelling of the algorithm.

## Project structure

The Lean code is organised into three subdirectories of `Isqrt`:

- `Isqrt/Definitions` contains the iterative and recursive implementations of
  the integer square root algorithm in Lean, along with supporting definitions
  of Python primitives and mirrors of the relevant Python exceptions. It also
  contains _statements_ (but not proofs) of what constitutes correctness for
  an `isqrt` implementation.
- `Isqrt/Proofs` contains proofs of the correctness statements in
  `Isqrt/Definitions/Specification`.
- `Isqrt/Tests` contains direct tests of the two `isqrt` implementations and supporting
  definitions using Lean's `#guard` command, passing in inputs and checking that the
  outputs are as expected.

The modules under `Isqrt/Proofs` are the only ones that depend on Mathlib, primarily for
the `linarith`, `ring` and `positivity` proof tactics. The definitions are Mathlib-free.

There are two root files: `Isqrt.lean` and `IsqrtTests.lean`. The
former imports the definitions and proofs; the latter imports the definitions and tests.
Both roots are marked as `@[default_target]` in `lakefile.lean`, so `lake build`
exercises the `#guard` checks.

## Validating the proof

This section describes how you can use Lean to validate the proof.

### Prerequisites

Install [elan](https://github.com/leanprover/elan) (the Lean version manager), following
the [instructions](https://github.com/leanprover/elan#installation) in the README for
that project. For example, on macOS or Linux you can use:

```
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

This should make `elan` and `lake` available on your `PATH`.

### Building the project

The key commands are all executed via Lean's build tool, `lake`. The first time you run `lake` it will automatically download the correct Lean toolchain version (as specified
in `lean-toolchain`). From this directory:

```
lake exe cache get   # download prebuilt Mathlib (avoids slow compilation from source)
lake build           # build the project
lake build --wfail   # build, failing on warnings too (matches CI)
lake lint            # check for style issues
```

The success of `lake build` (exit code 0, no displayed error messages) implies that
Lean was able to mechanically check every step of the proofs, and that the proofs are
correct. The stronger `lake build --wfail` turns warnings into errors. Notably, `lake
build` will still pass (with warnings) if there are incomplete proofs, marked by a
`sorry` placeholder in Lean. `lake build --wfail` will fail in the presence of `sorry`s.

## What do I need to trust?

The main goal of this project is to convince a reader that the Python code shown in the
overview section is correct. The success of the `lake build` step says that all the
proofs that Lean checked are valid. There are some dots to join between those two
things. A reader who wants to be convinced of the correctness of the Python code
needs to have confidence in:

- The faithfulness of the Python-to-Lean translation. If the Lean functions are
  executing a _different_ algorithm from the Python code shown earlier, then the
  correctness of the Lean code doesn't say much about the correctness of the Python
  code. In particular, this includes validating:
  - The `isqrtIterative` implementation in
    [Isqrt/Definitions/IsqrtIterative.lean](Isqrt/Definitions/IsqrtIterative.lean).
  - The definitions of the Python primitives: the Lean versions of Python's `>>`, `<<`
    and `//` operators, and the Lean versions of Python's `int.bit_length` and `range`.
    These definitions are all in
    [Isqrt/Definitions/PythonPrimitives.lean](Isqrt/Definitions/PythonPrimitives.lean).
  - The exception-related definitions in
    [Isqrt/Definitions/Exceptions.lean](Isqrt/Definitions/Exceptions.lean).
- The statements of correctness in
  [Isqrt/Definitions/Specification.lean](Isqrt/Definitions/Specification.lean),
  in particular the `isCorrectIsqrt` predicate.
- That the `lake build` validation run includes validating the _proof_ of the correctness
  statement. That proof lives right at the bottom of
  [Isqrt/Proofs/IterativeCorrectness.lean](Isqrt/Proofs/IterativeCorrectness.lean).
  The statement is simply: `theorem isCorrectIsqrt_isqrtIterative : isCorrectIsqrt isqrtIterative := ...`
- The Lean toolchain itself, including the compiler and standard library. It's
  conceivable (but highly unlikely) that Lean itself has bugs that mean that it reports
  validity of a proof that is actually invalid.

Things that *don't* need to be trusted:

- The contents of the proofs. No matter how gnarly the proofs look, if Lean says that
  they're valid, then they're valid.
- `Mathlib`. While the proofs use Mathlib, the definitions and statements of correctness
  do not. An error in `Mathlib` cannot cause Lean to accept an invalid proof as valid.

In terms of the file layout, it's enough to read through and validate everything under
`Isqrt/Definitions`, along with the one-line statement (but not the proof) of
`isCorrectIsqrt_isqrtIterative`. That's less than 250 lines of code total (including
comments, docstrings and blank lines). And in fact, some of those can be ignored:
the `isCorrectIsqrt_isqrtIterative` statement does not depend on the contents
of `Isqrt/Definitions/IsqrtRecursive.lean`, or on the definition of `isNearSquareRoot`
in `Isqrt/Definitions/Specification.lean`.

For the correctness of the recursive version, similar comments apply: look at
`Isqrt/Definitions` and the single-line statement (but not the proof) of
`isCorrectIsqrt_isqrtRecursive` in `Isqrt/Proofs/RecursiveCorrectness.lean`.

There are also empirical tests under `Isqrt/Tests`, for particular chosen
input values. While these aren't formal proofs, they provide easy-to-read
empirical evidence that the two `isqrt` implementations do the right thing.

## Notes on the Python-to-Lean translation

The goal of this proof is to give us confidence in the
integer square root algorithm behind CPython's `math.integer.isqrt`. We don't
prove anything about the Python code directly; instead, we translate
the relevant Python code into Lean and prove that the *Lean* code is
correct.

For that strategy to be worth anything, the translation has to be "high
fidelity" — close enough that correctness of the Lean version really
does imply correctness of the Python version. Lean and Python are very
different languages, so this isn't automatic.

Several of the translation choices in this project were made specifically to
support that high-fidelity claim. The subsections below walk through them.

Better still, the same choices turn the finished proof into a
*certificate* about the Python algorithm itself: because every operation
that can raise is modelled honestly, a successful run proves that no such
failure — division by zero, a negative shift, runaway recursion — can be
triggered by any valid input. The section "The `.ok` result is a
certificate" below makes that precise.

### The Python reference

Here is the recursive integer square root algorithm, in Python, that
the Lean development mirrors:

```python
def nsqrt(n: int, c: int) -> int:
    if c == 0:
        return 1
    else:
        k = (c - 1) // 2
        a = nsqrt(n >> 2 * k + 2, c // 2)
        return (a << k) + (n >> k + 2) // a

def isqrt(n: int) -> int:
    if n < 0:
        raise ValueError("isqrt() argument must be nonnegative")
    if n == 0:
        return 0
    c = (n.bit_length() - 1) // 2
    a = nsqrt(n, c)
    return a - 1 if n < a * a else a
```

This recursive form is the algorithm's original derivation, by the author of
CPython's `math.integer.isqrt`; it's also written up in [a Stack Overflow
answer][so-recursive], and reproduced as a docstring at the top of
`Isqrt/Definitions/IsqrtRecursive.lean`.

CPython itself ships an [iterative formulation][cpython-iterative] of
the same algorithm, derived from the recursive one for efficiency. That
formulation is verified here too: `isqrtIterative` (`Isqrt/Definitions/IsqrtIterative.lean`)
is a faithful, lightly-rewritten transcription of the CPython source
comment, with its `for s in reversed(range(c.bit_length()))` loop rendered
as Lean's own `for … in … do`. `isCorrectIsqrt_isqrtIterative`
(`Isqrt/Proofs/IterativeCorrectness.lean`) then proves it meets the same
specification as the recursive `isqrtRecursive`: it reduces the monadic `for … in`
loop to a `List.foldlM` over the reversed range and reuses the recursive
proof's per-iteration algebra unchanged.

[so-recursive]: https://stackoverflow.com/a/78076732
[cpython-iterative]: https://github.com/python/cpython/blob/v3.15.0b1/Modules/mathintegermodule.c#L191-L211

### Where the languages line up

Some of the translation is mechanical, because Python and Lean already agree
on the meaning (and often the syntax) of the operation:

- **Integers.** Python's `int` is arbitrary precision; Lean's `Int` is also
  arbitrary precision. There's no risk of overflow or truncation behaving
  differently in the two languages — `int` ↔ `Int` is a clean match.
- **Integer literals.** Small literals like `0`, `1`, `2` translate
  directly. There's a *bit* of hand-waving here: Python's `0` is
  unambiguously of type `int`, while Lean's numeric literals are
  polymorphic — `0` could in principle be a `Nat`, an `Int`, a rational,
  a real, etc., with the type determined by surrounding context. In the
  expressions we care about, the neighbouring `Int`-typed variables force
  the literal to be elaborated as `Int`, so the effective meaning is the
  same as on the Python side.
- **Ring operations.** Addition, negation, multiplication, and subtraction
  use the same symbols (`+`, `-`, `*`) in both languages and have identical
  semantics on integers. These never raise, so they translate directly —
  only `//`, `>>`, and `<<` need the `Except` treatment described below.
- **Order comparisons.** `<`, `<=`, `>`, `>=` likewise agree on both symbols
  and meanings.

### Why `Int` and not `Nat`

Lean has two natural choices of integer type: `Nat` (nonnegative integers
only) and `Int` (signed integers, arbitrary precision). The Lean 3
predecessor of this proof was written in `Nat` throughout. We could have
done the same here, but chose `Int` for two reasons:

- **Fidelity.** Python has one integer type, `int`, which is signed.
  Mapping `int` to `Int` is a direct match; mapping to `Nat` would mean
  the Lean code is talking about a type that Python doesn't actually
  have, and we'd be obliged to argue separately that no intermediate
  quantity ever goes negative.
- **Algebraic cleanliness.** `Nat` is closed under subtraction only by
  virtue of *truncating* subtraction (`2 - 5 = 0` in `Nat`, not `-3`).
  That makes ordinary algebraic manipulation subtle — the Lean 3 proof
  carries a substantial set of lemmas whose only purpose is to reason
  around truncating subtraction. With `Int`, ring arithmetic just
  works, and Lean's `ring` tactic discharges purely algebraic goals in
  a single step.

`Int` isn't free either: in places where the underlying mathematical
object is genuinely a natural number (the bit length of `n`, and the
counter used for the recursion), we have to bridge between
`Int` and `Nat` via `.toNat`. We pay some awkwardness either way — the
question is *where*, and we chose `Int`.

### Equality: `=` vs `==`

> **Lean details ahead.** A reader interested purely in the
> Python-fidelity story can skip this subsection — the short version is
> that the Lean test `if n = 0 then ...` has runtime behaviour
> identical to Python's `if n == 0:`. The rest of this subsection
> explains why, for readers who'd otherwise be suspicious of the `=`
> versus `==` mismatch.

Python's `==` takes two integers, compares them, and returns a Python
`bool`; that `bool` is then used by `if` to pick a branch. Lean has a
`==` operator that works similarly (returning something of type `Bool`),
but the Lean definitions in this project use `=` rather than `==` — for
example `if n = 0 then return 0` in `isqrtRecursive`. The `n = 0` here has
type `Prop`, which lives in proof-world rather than in the
concrete-computational-object world. At first glance that looks like the
wrong tool for a runtime conditional.

However, Lean's `if-then-else` doesn't just require a `Prop`: it
requires the proposition to be *decidable*. A `Decidable` instance for a
proposition `p` is, concretely, one of two things: either a proof that
`p` holds, or a proof that `¬p` holds. (It's an inductive type with two
constructors, `isTrue` and `isFalse`, each carrying the corresponding
proof — much like a `Bool` plus the matching proof.) Equality between integers is decidable,
so Lean supplies the procedure that constructs the instance
automatically, and the runtime semantics of the Lean function —
ignoring the proof layer — exactly match those of Python.

### Floor division

The Python algorithm makes heavy use of Python's `//`, `>>`, and `<<`
operators. This is where translation gets interesting. We'll focus on `//`
first; the story for `>>` and `<<` follows the same pattern.

Two features of Python's `//` need attention:

1. **Behaviour on negative inputs.** Python's `//` rounds toward minus
   infinity. Lean's default `Int` division operator `/` instead uses
   *Euclidean* division, which rounds toward zero. The two functions
   disagree whenever exactly one of the operands is negative and the
   division isn't exact. Lean's `Int.fdiv` matches Python's semantics
   exactly, so we'll use `Int.fdiv` as the underlying operation rather
   than `/`.

2. **Behaviour when the denominator is zero.** Python raises a
   `ZeroDivisionError`. Lean has no exceptions: if you ask `Int.fdiv`
   to divide by zero, it cheerfully returns a garbage value (in fact
   `0`) and the program keeps going.

The first concern is fully resolved by choosing `Int.fdiv` over `/`. The
second is harder: the Lean and Python functions disagree on division by
zero, and the Lean version is the more permissive of the two. There are
at least three reasonable ways to close that gap:

- **Option 1.** Translate Python `//` directly to `Int.fdiv` and live
  with the mismatch.
- **Option 2.** Translate Python `//` to a Lean function returning an
  `Except`-style result, carrying either the computed value or the
  exception Python would have raised.
- **Option 3.** Translate Python `//` to a 3-argument Lean function
  whose third argument is a *proof* that the denominator is nonzero.

We use **Option 2**. Option 1 is too weak — it would let us silently
build an algorithm that relied on dividing by zero. Option 3 also closes
the gap, but it makes the error case *unrepresentable*: you can't even
write a division down until you've proved it won't raise, so the "never
divides by zero" facts end up scattered across proof obligations at every
call site, and the function has to carry proof baggage in its signature
that Python's has no trace of. Option 2 keeps the function's shape honest
— its result is a value that is *either* the answer or the very exception
Python would raise — which lets us state a single *total* specification
covering both the success and the failure case (see "The `.ok` result is
a certificate" below).

Concretely, the Lean side defines a function `pyFloordiv` taking two
integers `a` and `b` and returning `PyExcept Int` (this project's
abbreviation for `Except PyException Int`): when `b = 0`
it returns `.error .zeroDivisionError`, mirroring Python's
`ZeroDivisionError`; otherwise it returns `.ok (Int.fdiv a b)`.

The obvious worry about Option 2 — that threading an `Except` through
every intermediate expression would drown the algorithm in plumbing — is
dissolved by Lean's `do`-notation. Inside a `do` block, binding a raising
operation with `←` (as in `let k ← pyFloordiv (c - 1) 2`) automatically
short-circuits to the error on `.error` and continues with the unwrapped
value on `.ok`. So each line that could raise in Python becomes a single
`←` bind in Lean, the surrounding code never mentions the `Except`
wrapper, and the translation reads almost verbatim like the Python
source — the monad does the plumbing, not the reader. (For a full
account of how Lean's `do`-notation desugars, see the paper
[*'do' unchained*][do-unchained].)

[do-unchained]: https://lean-lang.org/papers/do.pdf

### Shifts

Python's `<<` and `>>` operators raise a `ValueError` if their second
argument is negative. We handle this exactly the way we handled division
by zero — with `Except`:

- `pyLshift` and `pyRshift` return `PyExcept Int`. On a negative
  shift count they return `.error (.valueError "negative shift count")`;
  otherwise they are Lean's native `<<<` and `>>>` on `Int`, matching
  Python's semantics on all inputs — including a negative *first*
  argument, since `>>` is an arithmetic (floor) shift in both languages.
  We use the native operators rather than multiplying / floor-dividing by
  `2 ^ k`: shifting is linear in the operand's bit length, where multiply
  and divide are not. The `pyLshift_eq_ok` / `pyRshift_eq_ok` lemmas pin
  `<<<` / `>>>` to `· * 2 ^ k` / `Int.fdiv · (2 ^ k)` — the arithmetic form
  the correctness proofs reason about.
- As with `//`, each call site binds the result with `←` inside the `do`
  block, so Python's `n >> (2 * k + 2)` becomes
  `let nShift ← pyRshift n (2 * k + 2)` and the surrounding code never
  sees the `Except` wrapper explicitly.

### Bit length

Python's `int.bit_length()` returns the number of bits needed to
represent `abs(n)`, with `(0).bit_length() == 0`. Unlike `//`, `<<`, and
`>>`, this method can't raise on any integer input, so it needs no
`Except` wrapper — it's just a function. It's defined as `Int.bitLength` in
`Isqrt/Definitions/PythonPrimitives.lean`, alongside the operator mirrors it joins;
the lemmas about it live in `Isqrt/Proofs/PythonPrimitivesLemmas.lean`.

On the Lean side it's named `Int.bitLength : Int → Int` — invoked as
`n.bitLength`, mirroring Python's `n.bit_length()` — and defined as
`if n = 0 then 0 else Nat.log2 n.natAbs + 1`, on top of core Lean's
`Nat.log2`. (Zero is special-cased: `Nat.log2 0 = 0`, so the `+ 1` branch
would otherwise report one bit for it.) The intermediate trip through `Nat`
is one of the
bridging costs anticipated in "Why `Int` and not `Nat`" above: the
natural home for a bit-count is `Nat`, but the top-level signature
returns `Int` to keep the public interface uniformly integer-valued and
to match Python's signature (Python's `int.bit_length()` returns `int`,
not some separate "nonneg int" type).

### The counter `s`

The translation concerns so far have all been at the level of individual
Python operations. Two more appear at the level of the recursive function
itself, where Lean asks for things Python doesn't.

The first is **termination**. Python doesn't require a recursive function
to be proved terminating — in principle it could recurse forever, and in
practice it would eventually raise `RecursionError`. Lean requires every
recursive definition to be justified by a measure that provably decreases
on each call.

The second is specific to going monadic, and it's the interesting one.
The natural translation of `nsqrt` recurses on `c // 2` with `c == 0`
as the base case. But under Option 2 that division is a monadic
`let cHalf ← pyFloordiv c 2`, and the value `cHalf` bound by `←` is
*opaque* to Lean's termination checker: it has no way to see that `cHalf`
is smaller than `c`, so it won't accept `c // 2` as a decreasing measure.
(A verbatim `c // 2` recursion would also misbehave on negative input —
`(-1) // 2 = -1` in Python, so it would self-loop — but the size
conditions rule `c < 0` out; the termination checker's blindness is the
real obstacle.)

The fix is to recurse on something the checker *can* see, without giving
up the monadic division. We add an explicit counter `s : Nat`, seed it at
`c.bit_length()`, and recurse on `s`:

```
def nsqrtRecursive (n c : Int) (s : Nat) : PyExcept Int := do
  if s = 0 then
    return 1
  else
    let k ← (c - 1) // 2
    let a ← nsqrtRecursive (← n >> 2 * k + 2) (← c // 2) (s - 1)
    return (← a << k) + (← (← n >> k + 2) // a)
```

Lean accepts this as **well-founded** recursion: the counter strictly
decreases, `s - 1 < s` — valid because the `else` branch guarantees
`s ≠ 0` — and Lean discharges that obligation automatically, so there is
still no `termination_by` and no `decreasing_by`. The explicit `else`
earns its keep: with a bare early `return 1` and fall-through, do-notation
lifts the recursive call out of the `if`, hiding the `s ≠ 0` guard from
the termination checker; keeping the body in the `else` is what lets it
through. And because the recursion variable is `s`, the division `c // 2`
stays a genuine `pyFloordiv c 2` (written here with the local infix `//`,
as are `<<` and `>>` for `pyLshift` and `pyRshift`): every operation that
can raise in Python is still an honest monadic `←` bind — as is the
recursive call — illustrating the `do`-block claim from "Floor division",
and the body otherwise reads almost like the Python.

`s` has no counterpart in the Python source; it's pure Lean scaffolding.
What makes it faithful is that it tracks `c.bit_length()` exactly. For
`c > 0` we have `(c // 2).bit_length() = c.bit_length() - 1`, so seeding
`s = c.bit_length()` makes the counter fall by exactly one per recursive
step and reach `0` at precisely the moment `c` does — so `if s = 0`
reproduces the `if c == 0` base case faithfully. The invariant has to be
*tight*: seeding `s` too large would let the recursion run past `c = 0`,
where `k = (c - 1) // 2 = -1` and the body's `a << k` would raise a
`ValueError`. Accordingly the correctness proof carries
`s = c.bit_length()` — not merely `s ≥ c.bit_length()` — as an invariant.

The recursive body also divides by the result of the recursive call,
`(n >> (k + 2)) // a`, which in Python would raise if `a` were ever `0`.
Under Option 2 that's just one more `←` bind; no special return type is
needed to thread a positivity proof out of the recursion. The correctness
proof shows `a > 0` at every step, so that `.error` branch is never taken
— one more strand of the certificate below.

Finally, the counter unifies the two formulations. Seeding it at
`c.bit_length()` makes the recursion run exactly as many steps as
CPython's *iterative* loop, `for s in reversed(range(c.bit_length()))`,
runs iterations. (The two `s`'s aren't the same quantity — here `s`
counts the steps still to come, while the loop's `s` is the shift amount
at each step — but both walk `c.bit_length()` rungs from the top down to
zero.) The recursive and iterative translations therefore share a
skeleton, which is why their correctness proofs can share the same
per-iteration algebra (`key_isqrt_lemma` in `Isqrt/Proofs/KeyLemma.lean`).

### The `.ok` result is a certificate

Modelling every raising operation with `Except` does more than keep the
translation honest — it turns the finished proof into a certificate about
the Python algorithm.

The top-level theorems are *total* specifications. Both
`isCorrectIsqrt_isqrtRecursive` and its iterative twin
`isCorrectIsqrt_isqrtIterative` prove the same contract, `isCorrectIsqrt`
(in `Isqrt/Definitions/Specification.lean`), which states the two properties
we want of an `isqrt` implementation `f`, one for each sign of the argument:

```
def isCorrectIsqrt (isqrt : Int → PyExcept Int) : Prop :=
  (∀ n, 0 ≤ n → ∃ a, returns (isqrt n) a ∧ isIntegerSquareRoot n a)
  ∧
  (∀ n, n < 0 → raises (isqrt n) (.valueError "isqrt() argument must be nonnegative"))
```

Here `returns (isqrt n) a` asserts that `isqrt n` took the `.ok` branch with value
`a`, and `raises (isqrt n) e` that it took the `.error` branch with exception `e` —
each is just the corresponding `Except` equality (`isqrt n = .ok a` and
`isqrt n = .error e`). So the first clause reads "for nonnegative `n`, `f n` returns
some `a`, and that `a` is `⌊√n⌋`"; the second, "for negative `n`, `f n` raises exactly
the `ValueError` Python raises for negative input, message and all." (`returns` and
`raises` are defined in `Isqrt/Definitions/Specification.lean`, rather than grafted
onto `Except`.)

That is the certificate. A `do` block short-circuits to `.error` the
moment any operation raises, so the only way `isqrtRecursive n` can return (be
`.ok`) is if *no* operation raised along the way. The theorem proves
`isqrtRecursive n` returns for every `n ≥ 0` — which means that for every
nonnegative input:

- no `//` was handed a zero divisor (no `ZeroDivisionError`),
- no `<<` or `>>` saw a negative shift count (no `ValueError` from a shift),
- and the recursion bottomed out (no runaway recursion).

The proof-carrying Option 3 would have established these as three separate
facts, discharged at scattered call sites. Under Option 2 they are
corollaries of one theorem about one return value.
