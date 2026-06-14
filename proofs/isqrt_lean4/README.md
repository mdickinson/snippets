# Correctness proof for CPython's `math.integer.isqrt`

This repository provides a formal proof of correctness, in Lean, of the algorithm
underlying the CPython implementation of Python's `math.integer.isqrt` function.

## Overview

Python's `math.integer.isqrt` standard library function (`math.isqrt` prior to Python
3.15) computes the integer square root of a nonnegative integer `n`: the unique
integer `a` satisfying `a * a <= n < (a + 1) * (a + 1)`.

The function is implemented in C, but the source code describes an equivalent Python
implementation. Here's that implementation. (Sources: [original
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

Despite its simplicity, the algorithm is unpublished and novel, and in places quite
delicate, so skepticism about its correctness is warranted. This repository provides a
direct, faithful translation of the above algorithm into the Lean programming language,
along with a formal machine-checkable proof of correctness of that translation.

While the iterative version above is what's implemented in CPython, the algorithm as
originally derived was recursive, and is clearer when expressed that way. This
repository therefore also contains a definition and proof of correctness for the
recursive variant of the algorithm.

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

From this directory:

```
lake exe cache get   # download prebuilt Mathlib (avoids compiling from source)
lake build           # build the project
lake build --wfail   # build, failing on warnings too (matches CI)
lake lint            # check for style issues
```

The first `lake` command you run will automatically download the correct
Lean toolchain version (specified in `lean-toolchain`).

Downloading the Mathlib cache (`lake exe cache get`) fetches ~1-2 GB of
prebuilt `.olean` files. Without this step, `lake build` would compile
all of Mathlib from source, which takes several hours.


## Project structure

The library is organised into three components, each a subdirectory of `Isqrt/`:

- **`Definitions/`** — the trust surface: Lean mirrors of the Python operations,
  the two `isqrt` translations, and the integer-square-root specification
  predicate. This is the part a reader must check against Python (see "What do I
  need to trust?" below).
- **`Proofs/`** — the correctness theorems and every supporting lemma. A reader
  who trusts Lean's checker can skip all of it beyond the *statements* of the two
  top-level theorems.
- **`Tests/`** — the `#guard` sanity checks.

The dependency direction is one-way: `Proofs/` and `Tests/` both build on
`Definitions/`, neither depends on the other, and `Definitions/` depends on
nothing else in the project. (Lean doesn't enforce this across a single package;
it's a convention the directory split keeps visible in review.)

```
lakefile.lean                  -- project configuration and dependencies
lean-toolchain                 -- Lean version pin
Isqrt.lean                     -- library root (imports Definitions + Proofs)
IsqrtTests.lean                -- tests root (imports the #guard files)
Isqrt/
  Definitions.lean             -- component root: the trust surface
  Definitions/
    PythonOps.lean             -- PyException + Except-returning //, >>, <<, and range
    BitLength.lean             -- natBitLength / pyBitLength definitions
    IntegerSquareRoot.lean     -- isIntegerSquareRoot specification predicate
    Algorithm.lean             -- recursive isqrtAux and isqrt definitions
    Iterative.lean             -- iterative isqrtIterative definition (Lean for … in loop)
  Proofs.lean                  -- component root: theorems and supporting lemmas
  Proofs/
    FDivLemmas.lean            -- Int.fdiv ordering lemmas and Int↔ℕ bridge
    BitLengthLemmas.lean       -- power-of-two / floor-division facts about pyBitLength
    PythonOpsLemmas.lean       -- .ok-branch value-extraction lemmas for the operators
    SizeConditions.lean        -- size-condition invariants + isqrt_c_nonneg recursion-depth seed
    KeyLemma.lean              -- key algebraic lemma; isNearSquareRoot predicate
    Correctness.lean           -- recursive correctness proof (isqrt_eq_ok_iff)
    IterativeCorrectness.lean  -- iterative correctness proof (isqrtIterative_eq_ok_iff)
  Tests/
    Assertions.lean            -- assert* helpers shared by both test files
    Iterative.lean             -- #guard checks for the Python ops and isqrtIterative
    Isqrt.lean                 -- #guard checks for the recursive isqrt
```

Both roots are `@[default_target]` in `lakefile.lean`, so `lake build` exercises
the `#guard` checks. The implementation library does not import the tests.

## Python-to-Lean translation

The goal of this proof is to give us confidence in the recursive
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
def isqrt_aux(c: int, n: int) -> int:
    if c == 0:
        return 1
    else:
        k = (c - 1) // 2
        a = isqrt_aux(c // 2, n >> (2 * k + 2))
        return (a << k) + (n >> (k + 2)) // a

def isqrt(n: int) -> int:
    if n == 0:
        return 0
    else:
        c = (n.bit_length() - 1) // 2
        a = isqrt_aux(c, n)
        return a - 1 if n < a * a else a
```

It's closely adapted from [a Stack Overflow answer][so-recursive] by
the same author who designed the algorithm and wrote CPython's
`math.integer.isqrt`. The code is also reproduced as a docstring at the top of
`Isqrt/Definitions/Algorithm.lean`.

CPython itself ships an [iterative formulation][cpython-iterative] of
the same algorithm, derived from the recursive one for efficiency. That
formulation is verified here too: `isqrtIterative` (`Isqrt/Definitions/Iterative.lean`)
is a faithful, lightly-rewritten transcription of the CPython source
comment, with its `for s in reversed(range(c.bit_length()))` loop rendered
as Lean's own `for … in … do`. `isqrtIterative_eq_ok_iff`
(`Isqrt/Proofs/IterativeCorrectness.lean`) then proves it meets the same
specification as the recursive `isqrt`: it reduces the monadic `for … in`
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
structural counter used for the recursion), we have to bridge between
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
example `if n = 0 then return 0` in `isqrt`. The `n = 0` here has
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
integers `a` and `b` and returning `Except PyException Int`: when `b = 0`
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
source — the monad does the plumbing, not the reader.

### Shifts

Python's `<<` and `>>` operators raise a `ValueError` if their second
argument is negative. We handle this exactly the way we handled division
by zero — with `Except`:

- `pyLshift` and `pyRshift` return `Except PyException Int`. On a negative
  shift count they return `.error (.valueError "negative shift count")`;
  otherwise they match Python's semantics on all inputs, including the
  cases where the *first* argument is negative. (Python and Lean both
  define those uniformly: `<<` is multiplication by a power of two, `>>`
  is floor-division by a power of two.)
- As with `//`, each call site binds the result with `←` inside the `do`
  block, so Python's `n >> (2 * k + 2)` becomes
  `let nShift ← pyRshift n (2 * k + 2)` and the surrounding code never
  sees the `Except` wrapper explicitly.

### Bit length

Python's `int.bit_length()` returns the number of bits needed to
represent `abs(n)`, with `(0).bit_length() == 0`. Unlike `//`, `<<`, and
`>>`, this method can't raise on any integer input, so it needs no
`Except` wrapper — it's just a function. Its definition lives in
`Isqrt/Definitions/BitLength.lean` (with the operator definitions in
`Isqrt/Definitions/PythonOps.lean`, but in its own module, since it's a
separate concept); the lemmas about it live in
`Isqrt/Proofs/BitLengthLemmas.lean`.

On the Lean side it's named `pyBitLength : ℤ → ℤ`, defined as
`natBitLength n.natAbs` (where `natBitLength : ℕ → ℕ` is built on top of
core Lean's `Nat.log2`). The intermediate trip through `ℕ` is one of the
bridging costs anticipated in "Why `Int` and not `Nat`" above: the
natural home for a bit-count is `ℕ`, but the top-level signature
returns `ℤ` to keep the public interface uniformly integer-valued and
to match Python's signature (Python's `int.bit_length()` returns `int`,
not some separate "nonneg int" type).

### The structural counter `s`

The translation concerns so far have all been at the level of individual
Python operations. Two more appear at the level of the recursive function
itself, where Lean asks for things Python doesn't.

The first is **termination**. Python doesn't require a recursive function
to be proved terminating — in principle it could recurse forever, and in
practice it would eventually raise `RecursionError`. Lean requires every
recursive definition to be justified by a measure that provably decreases
on each call.

The second is specific to going monadic, and it's the interesting one.
The natural translation of `isqrt_aux` recurses on `c // 2` with `c == 0`
as the base case. But under Option 2 that division is a monadic
`let cHalf ← pyFloordiv c 2`, and the value `cHalf` bound by `←` is
*opaque* to Lean's termination checker: it has no way to see that `cHalf`
is smaller than `c`, so it won't accept `c // 2` as a decreasing measure.
(A verbatim `c // 2` recursion would also misbehave on negative input —
`(-1) // 2 = -1` in Python, so it would self-loop — but the size
conditions rule `c < 0` out; the termination checker's blindness is the
real obstacle.)

The fix is to recurse on something the checker *can* see, without giving
up the monadic division. We add an explicit counter `s : ℕ`, seed it at
`c.bit_length()`, and recurse **structurally** on `s`:

```
def isqrtAux (s : ℕ) (c n : Int) : Except PyException Int :=
  match s with
  | 0 => pure 1
  | s + 1 => do
    let k ← pyFloordiv (c - 1) 2
    let cHalf ← pyFloordiv c 2
    let nShift ← pyRshift n (2 * k + 2)
    let a ← isqrtAux s cHalf nShift
    let lsh ← pyLshift a k
    let rsh ← pyRshift n (k + 2)
    let q ← pyFloordiv rsh a
    pure (lsh + q)
```

Structural recursion on `s` is accepted automatically — `s` literally
loses a constructor on each call — so there is no `termination_by` and no
`decreasing_by`. And because the recursion variable is now `s`, the
division `c // 2` stays a genuine `pyFloordiv c 2`: every operation that
can raise in Python is still an honest monadic `←` bind. (Notice this also
illustrates the `do`-block claim from "Floor division": each of the six
raising operations is a single `←` bind — as is the recursive call — and
the body otherwise reads almost like the Python.)

`s` has no counterpart in the Python source; it's pure Lean scaffolding.
What makes it faithful is that it tracks `c.bit_length()` exactly. For
`c > 0` we have `(c // 2).bit_length() = c.bit_length() - 1`, so seeding
`s = c.bit_length()` makes the counter fall by exactly one per recursive
step and reach `0` at precisely the moment `c` does — so `match s`
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

The top-level theorems are *total* specifications. `isqrt_eq_ok_iff`
(and its iterative twin `isqrtIterative_eq_ok_iff`) characterise the
result by cases:

```
match isqrt n with
| .ok v    => 0 ≤ n ∧ isIntegerSquareRoot v n
| .error e => n < 0 ∧ e = .valueError "isqrt() argument must be nonnegative"
```

Read the two branches together. The `.error` branch is pinned to a single
possibility: the *only* error the function can return is the `ValueError`
Python raises for negative input, and it returns that error for exactly
the negative inputs. Every other input — every `n ≥ 0` — lands in the
`.ok` branch with `v = ⌊√n⌋`.

That is the certificate. A `do` block short-circuits to `.error` the
moment any operation raises, so the only way `isqrt n` can be `.ok` is if
*no* operation raised along the way. The theorem proves `isqrt n` is `.ok`
for every `n ≥ 0` — which means that for every nonnegative input:

- no `//` was handed a zero divisor (no `ZeroDivisionError`),
- no `<<` or `>>` saw a negative shift count (no `ValueError` from a shift),
- and the recursion bottomed out (no runaway recursion).

The proof-carrying Option 3 would have established these as three separate
facts, discharged at scattered call sites. Under Option 2 they are
corollaries of one theorem about one return value.

### What do I need to trust?

If you're reading this repository hoping to come away with confidence
that Python's `math.integer.isqrt` is correct, here's where to put your attention
— and where you can let your guard down.

**Read carefully.** The fidelity of the translation lives in two places:

- The Lean *definitions* of `isqrt` and `isqrtAux` (in
  `Isqrt/Definitions/Algorithm.lean`), of `isqrtIterative` (in
  `Isqrt/Definitions/Iterative.lean`), of the `pyFloordiv` / `pyRshift` /
  `pyLshift` operations (in `Isqrt/Definitions/PythonOps.lean`), and of
  `pyBitLength` (in `Isqrt/Definitions/BitLength.lean`) — that is, everything
  under `Isqrt/Definitions/`. These are the only places where a
  translation error could plausibly creep in: if a Lean function isn't
  actually computing the same thing as the Python function it claims to
  mirror, the proof is proving something about a different algorithm.
- The *statements* of the correctness theorems `isqrt_eq_ok_iff` (in
  `Isqrt/Proofs/Correctness.lean`) and `isqrtIterative_eq_ok_iff` (in
  `Isqrt/Proofs/IterativeCorrectness.lean`). This is where we say what "correct"
  means. Each is a total specification by cases on the result, spelled out
  in "The `.ok` result is a certificate" above: on `.ok v` it asserts
  `0 ≤ n` and `isIntegerSquareRoot v n` — where the predicate
  `isIntegerSquareRoot a n` (in `Isqrt/Definitions/IntegerSquareRoot.lean`) unfolds to
  `a * a ≤ n ∧ n < (a + 1) * (a + 1)`, i.e. `a` is the floor of √n — and
  on `.error e` it pins `e` to exactly Python's `ValueError`. If a
  statement (or the predicate) is too weak, the proof being valid doesn't
  buy us what we wanted.

**Trust without rereading.** The proofs of theorems and lemmas don't
require human verification. Lean's job is to check them, and if `lake
build` succeeds, then — modulo trusting Lean itself, and the Mathlib
library it depends on — every proof in the repository has been verified.
A reader looking for confidence in the result doesn't need to follow
individual proof steps.

**Sanity check.** Beyond the proofs, the repository contains
`#guard`-based tests (in `Isqrt/Tests/`) that exercise `isqrt`,
`isqrtIterative`, `pyFloordiv`, `pyRshift`, `pyLshift`, and `pyBitLength`
on concrete inputs and verify the outputs against expected values. These
tests are load-bearing in a way the proofs aren't: a proof can only ever
talk about the Lean definitions, so if a Lean definition silently
disagrees with its Python counterpart, the proof won't catch it. Running
the Python and Lean operations on the same inputs and comparing outputs is
exactly the check that fills that gap.
