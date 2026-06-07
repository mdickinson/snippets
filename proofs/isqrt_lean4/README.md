# Correctness proof for CPython's `math.isqrt`

A formal proof in Lean 4 of correctness for the integer square root
algorithm behind CPython's `math.isqrt` — both the original recursive
formulation and the iterative formulation that CPython ships.

## Prerequisites

Install [elan](https://github.com/leanprover/elan) (the Lean version manager):

```
curl https://elan.dev/install.sh -sSf | sh
```

## Building

From this directory:

```
lake exe cache get   # download prebuilt Mathlib (avoids compiling from source)
lake build           # build the project
```

The first `lake` command you run will automatically download the correct
Lean toolchain version (specified in `lean-toolchain`).

Downloading the Mathlib cache (`lake exe cache get`) fetches ~1-2 GB of
prebuilt `.olean` files. Without this step, `lake build` would compile
all of Mathlib from source, which takes several hours.

## Project structure

```
lakefile.lean              -- project configuration and dependencies
lean-toolchain             -- Lean version pin
Isqrt.lean                 -- library root (implementation modules)
IsqrtTests.lean            -- tests root (imports the #guard files)
Isqrt/
  PythonOps.lean           -- Lean definitions matching Python's //, >>, <<, bit_length
  FDivLemmas.lean          -- Int.fdiv ordering lemmas and Int↔ℕ bridge
  BitLengthLemmas.lean     -- natBitLength / pyBitLength properties
  KeyLemma.lean            -- key algebraic lemma; isNearSqrt / isIntegerSqrt predicates
  SizeConditions.lean      -- size-condition invariants carried through the recursion
  Algorithm.lean           -- isqrt_aux and isqrt definitions
  Correctness.lean         -- correctness proofs (isqrt_aux_correctness, isqrt_is_sqrt)
  Tests/
    PythonOps.lean         -- #guard checks for the Python operations
    Isqrt.lean             -- #guard checks for isqrt on concrete values
```

Both roots are `@[default_target]` in `lakefile.lean`, so `lake build` exercises
the `#guard` checks. The implementation library does not import the tests.

## Related files

- `../isqrt/` — the original Lean 3 proof (kept for reference)
- `../../snippets/isqrt.py` — Python implementations of the algorithm

## Python-to-Lean translation

The goal of this proof is to give us confidence in the recursive
integer square root algorithm behind CPython's `math.isqrt`. We don't
prove anything about the Python code directly; instead, we translate
the relevant Python code into Lean and prove that the *Lean* code is
correct.

For that strategy to be worth anything, the translation has to be "high
fidelity" — close enough that correctness of the Lean version really
does imply correctness of the Python version. Lean and Python are very
different languages, so this isn't automatic.

Several of the translation choices in this project were made specifically to
support that high-fidelity claim. The subsections below walk through them.

As a bonus, several of those choices also yield certificates about the
Python algorithm itself — for example, that particular failure modes
(like dividing by zero, or recursing forever) can never be triggered by
any input. We flag these as **By-product:** notes in the subsections
where they arise.

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
`math.isqrt`. The code is also reproduced as a docstring at the top of
`Isqrt/Algorithm.lean`.

CPython itself ships an [iterative formulation][cpython-iterative] of
the same algorithm, derived from the recursive one for efficiency. That
formulation is verified here too: `isqrtIterative` (`Isqrt/Iterative.lean`)
is a faithful, lightly-rewritten transcription of the CPython source
comment, and `isqrtIterative_is_sqrt` (`Isqrt/IterativeCorrectness.lean`)
proves it meets the same specification as the recursive `isqrt`, reusing
the recursive proof's algebra through a generic `while`-loop combinator
(`Isqrt/While.lean`). See `PLAN.md` and `CONTEXT.md` for that development.

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
  semantics on integers.
- **Order comparisons.** `<`, `<=`, `>`, `>=` likewise agree on both symbols
  and meanings.
- **Operator precedences (engineered).** The custom `py//`, `py>>`,
  `py<<` operators defined in `Isqrt/PythonOps.lean` are given
  precedences chosen to match Python's: `py//` binds like `*`, `py>>`
  and `py<<` bind looser than `+`, and all of them bind tighter than
  the comparison operators. So expressions parse the same way in both
  languages.

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
recursion-depth measure used to prove termination), we have to bridge
between `Int` and `Nat` via `.toNat`. We pay some awkwardness either
way — the question is *where*, and we chose `Int`.

### Equality: `=` vs `==`

> **Lean details ahead.** A reader interested purely in the
> Python-fidelity story can skip this subsection — the short version is
> that the Lean test `if _ : c = 0 then ...` has runtime behaviour
> identical to Python's `if c == 0:`. The rest of this subsection
> explains why, for readers who'd otherwise be suspicious of the `=`
> versus `==` mismatch.

Python's `==` takes two integers, compares them, and returns a Python
`bool`; that `bool` is then used by `if` to pick a branch. Lean has a
`==` operator that works similarly (returning something of type `Bool`),
but the Lean definitions in this project use `=` rather than `==` — for
example `if _ : c = 0 then ...` in `isqrt_aux`. The `c = 0` here has
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

Moreover, the *dependent* form of `if-then-else` — which is what's used
here — routes the proof into each branch: a proof of `c = 0` in the
`then` branch, a proof of `c ≠ 0` in the `else` branch. These
hypotheses are exactly the form Lean's arithmetic tactics (like `omega`)
consume directly, so downstream proofs are slightly more streamlined
than they'd be if we'd compared via `==` and had to bridge from
`(c == 0) = false` back to `c ≠ 0` by hand.

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
  `Except`-style result, carrying either the result or an error.
- **Option 3.** Translate Python `//` to a 3-argument Lean function
  whose third argument is a *proof* that the denominator is nonzero.

We use Option 3. Option 1 is too weak — it would let us silently build
an algorithm that relied on dividing by zero. Option 2 gives us the
rigor we want, but threading `Except` values through every intermediate
expression is much more painful than discharging a proof obligation at
the call site.

Concretely, the Lean side defines a function `pyFloordiv` taking two
integers `a` and `b` and a proof that `b` is nonzero. Each call site has
to supply that proof before the division is allowed to happen.

To keep this ergonomically tolerable, we add two conveniences:

- The proof argument has a *default value* of `by omega`. In practice,
  whenever the surrounding context already knows the divisor is nonzero
  (which it usually does), the proof is discharged automatically and the
  caller writes the division as if it took only two arguments.
- We define an infix operator `py//` that calls `pyFloordiv`. It would
  have been nicer to reuse `//` itself, but that symbol is already spoken
  for in Lean's parser. So `(c - 1) py// 2` reads as closely to Python's
  `(c - 1) // 2` as Lean's syntax allows.

**By-product:** every `//` in the Python algorithm corresponds to a
Lean call site that has to discharge `b ≠ 0`, so the correctness proof
also certifies that no `//` in the Python version can ever raise
`ZeroDivisionError`.

### Shifts

Python's `<<` and `>>` operators raise a `ValueError` if their second
argument is negative. We handle this exactly the way we handled
division by zero:

- Define Lean functions `pyLshift` and `pyRshift` that match Python's
  semantics on all inputs with nonnegative second argument — including
  the cases where the *first* argument is negative. (Python and Lean
  both define those uniformly: `<<` is multiplication by a power of
  two, `>>` is floor-division by a power of two.)
- Have each function take a third argument: a *proof* that the second
  argument is nonnegative, with the same `by omega` default as for
  `//`.
- Define infix operators `py<<` and `py>>` with the same relative
  precedence as Python's. We can't reuse `>>` itself — it's already
  spoken for as Lean's monadic "and then" operator.

**By-product:** the correctness proof also certifies that no `<<` or
`>>` in the Python version can raise `ValueError`.

### Bit length

Python's `int.bit_length()` returns the number of bits needed to
represent `abs(n)`, with `(0).bit_length() == 0`. Unlike `//`, `<<`, and
`>>`, this method can't raise on any integer input, so we don't need to
attach a proof obligation at call sites; it's just a function.

On the Lean side it's named `pyBitLength : ℤ → ℤ`, defined as
`natBitLength n.natAbs` (where `natBitLength : ℕ → ℕ` is built on top of
core Lean's `Nat.log2`). The intermediate trip through `ℕ` is one of
the bridging costs anticipated in "Why `Int` and not `Nat`" above: the
natural home for a bit-count is `ℕ`, but the top-level signature
returns `ℤ` to keep the public interface uniformly integer-valued and
to match Python's signature (Python's `int.bit_length()` returns `int`,
not some separate "nonneg int" type).

### Proof-carrying signatures

So far the translation concerns have all been at the level of
individual Python operations. The next two subsections move up to the
algorithm itself, where Lean requires things Python doesn't.

The first of these is at the function-signature level. The algorithm's
top-level functions carry their own preconditions: `isqrt` takes a
proof `0 ≤ n`, and `isqrt_aux` takes proofs `0 ≤ c` and `0 ≤ n`. (Both
default to `by omega`, the same convenience used for the Python
operators.) These nonnegativity hypotheses are needed to discharge the proof
obligations on the operators and on the recursive call inside the
body.

`isqrt_aux` adds one more twist that doesn't appear anywhere else in
the proof: it doesn't return a plain integer. Its return type is the
subtype `{ a : ℤ // 0 < a }` — a pair of an integer together with a
proof that it's strictly positive. The reason is the recursive case,
which contains an expression of the form `... + (n py>> (k + 2)) py// a`.
The `py// a` requires a proof that `a ≠ 0`, and since `a` is the
result of a recursive call, that proof has to come out of the
recursion. The cleanest way to thread it through is to bundle the
proof into the return type itself: every `isqrt_aux` result comes with
a witness that it's positive, and a caller writes
`let ⟨a, a_pos⟩ := isqrt_aux ...` to unpack both pieces.

### Termination of `isqrt_aux`

The other thing Lean asks for that Python doesn't is that every
recursive function be proved to terminate on all inputs. Python's
`isqrt_aux` is recursive, but Python doesn't require any such
guarantee — in principle a recursive Python function could call
itself forever; in practice it eventually hits the interpreter's
recursion limit and raises `RecursionError`. Either way, "this
terminates" isn't part of the language's contract.

This has visible cost in the Lean definition of `isqrt_aux`. At the
end of the `def` you'll find two extra clauses:

```
termination_by c.toNat
decreasing_by
  simp_wf
  exact fdiv_two_decreasing c_nonneg ‹¬c = 0›
```

These have no analog in Python. They tell Lean that the natural number
`c.toNat` strictly decreases on every recursive call, which — via the
standard well-founded recursion principle on `Nat` — is enough to
guarantee that recursion bottoms out after finitely many steps.

**By-product:** the correctness proof also rules out the Python version
recursing indefinitely.

### What do I need to trust?

If you're reading this repository hoping to come away with confidence
that Python's `math.isqrt` is correct, here's where to put your attention
— and where you can let your guard down.

**Read carefully.** The fidelity of the translation lives in two places:

- The Lean *definitions* of `isqrt` and `isqrt_aux` (in
  `Isqrt/Algorithm.lean`) and the `pyFloordiv` / `pyRshift` / `pyLshift`
  / `pyBitLength` operations (in `Isqrt/PythonOps.lean`). These are the
  only places where a translation error could plausibly creep in: if a
  Lean function isn't actually computing the same thing as the Python
  function it claims to mirror, the proof is proving something about a
  different algorithm.
- The *statement* of the correctness theorem `isqrt_is_sqrt` (in
  `Isqrt/Correctness.lean`). This is where we say what "correct" means.
  Concretely, the theorem asserts `isIntegerSqrt (isqrt n hn) n`, where the
  predicate `isIntegerSqrt a n` (in `Isqrt/KeyLemma.lean`) unfolds to
  `a * a ≤ n ∧ n < (a + 1) * (a + 1)` — i.e., `a` is the floor of √n. If the
  statement (or the predicate) is too weak, the proof being valid doesn't buy
  us what we wanted.

**Trust without rereading.** The proofs of theorems and lemmas don't
require human verification. Lean's job is to check them, and if `lake
build` succeeds, then — modulo trusting Lean itself, and the Mathlib
library it depends on — every proof in the repository has been verified.
A reader looking for confidence in the result doesn't need to follow
individual proof steps.

**Sanity check.** Beyond the proofs, the repository contains
`#guard`-based tests (in `Isqrt/Tests/`) that exercise `isqrt`,
`pyFloordiv`, `pyRshift`, `pyLshift`, and `pyBitLength` on concrete
inputs and verify the outputs against expected values. These tests are
load-bearing in a way the proofs aren't: a proof can only ever talk
about the Lean definitions, so if a Lean definition silently disagrees
with its Python counterpart, the proof won't catch it. Running the
Python and Lean operations on the same inputs and comparing outputs is
exactly the check that fills that gap.
