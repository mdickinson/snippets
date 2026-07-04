# Formal proof of correctness for Python's isqrt algorithm

This repository provides a formal machine-verifiable proof of correctness of the
algorithm underlying the CPython implementation of Python's `math.integer.isqrt`
function. It starts with a version of the algorithm written in Python, translates that
into Lean, and then proves correctness of the translated version.

## Overview

Python's [`math.integer.isqrt`][math-integer-isqrt] standard library function
(`math.isqrt` prior to Python 3.15) computes the [integer square
root][integer-square-root] of a nonnegative integer `n`: the unique integer `a`
satisfying `a * a <= n < (a + 1) * (a + 1)`.

The function is implemented in C, but the CPython source code describes an equivalent
Python implementation, which the C implementation follows closely. Here's that
implementation. (Sources: [original commit][math-isqrt-github-original] for Python 3.8;
[current home][math-integer-isqrt-github-current] in `math.integer`.)

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
delicate, so it's not unreasonable to question its correctness. This repository provides
evidence of the correctness of the algorithm in the form of a faithful line-by-line
translation of the above algorithm into the [Lean programming language][lean], along
with a formal machine-checkable proof of correctness of that translation.

While the iterative presentation above is what's implemented in CPython, the algorithm
as originally derived was recursive, and is conceptually clearer when presented that
way. This repository also contains a definition and proof of correctness for a recursive
spelling of the algorithm.

## Project structure

The Lean source code is organised into three subdirectories of [`Isqrt`](Isqrt):

- [`Isqrt/Definitions`](Isqrt/Definitions) contains the iterative and recursive
  implementations of the integer square root algorithm in Lean, along with supporting
  definitions of Python primitives and mirrors of the relevant Python exceptions. It
  also contains _statements_ (but not proofs) of what constitutes correctness for an
  implementation of integer square root - see
  [`Isqrt/Definitions/Specification.lean`](Isqrt/Definitions/Specification.lean) for
  those statements.
- [`Isqrt/Proofs`](Isqrt/Proofs) contains proofs of the correctness statements, along
  with supporting lemmas.
- [`Isqrt/Tests`](Isqrt/Tests) contains direct tests of the two `isqrt` implementations
  and supporting definitions using Lean's `#guard` command, passing in inputs and
  checking that the outputs are as expected.

In addition to the files under [`Isqrt`](Isqrt), there are three root files:
[`Isqrt.lean`](Isqrt.lean), [`IsqrtTests.lean`](IsqrtTests.lean) and
[`Main.lean`](Main.lean). The first imports the definitions and proofs; the second
imports the tests; the third contains the source for the `isqrt` command-line executable
described below.

The project does not depend on [Mathlib][mathlib]: its proofs, definitions and tests are
written using only Lean's core library. The sole external dependency is
[Batteries][batteries], and that only to provide the linter (`lake lint`) — no Batteries
code is used in the proofs themselves.

## Validating the proof

This section describes how you can use Lean to validate the proof, starting from the
directory containing this README file.

### Prerequisites

Install [elan][elan] (the Lean version manager), following the [installation
instructions][elan-installation] in the README for that project. Check that `elan` and
`lake` are available on your `PATH`.

### Building the project

The key commands are all executed via Lean's build tool, `lake`. The first time you run
`lake` it will automatically download the correct Lean toolchain version (as specified
in `lean-toolchain`). From this directory:

```
lake build            # build the project - definitions, proofs, tests and executable
lake build --wfail    # build, failing on warnings too (matches CI)
lake exe isqrt 1729   # run the command-line executable (should print 41)
lake lint             # check for style issues
```

The success of `lake build` (exit code 0, no displayed error messages) implies that
Lean was able to mechanically check every step of the proofs, and that the proofs are
correct. The stronger `lake build --wfail` turns warnings into errors. Notably, `lake
build` will still pass (with warnings) if there are incomplete proofs, marked by a
`sorry` placeholder in Lean. `lake build --wfail` will fail in the presence of `sorry`s.

## Running the algorithm

The project also includes a command-line executable `isqrt` that computes integer square
roots via the same `isqrtIterative` function that's proved correct in the proofs. It can
be executed via `lake exe isqrt`:

```console
$ lake exe isqrt 1729
41
```

The single argument must be a nonnegative integer.

The executable is backed by the correctness proof — it is that proof which guarantees
the computation never raises — yet the proof forms no part of the compiled program: Lean
erases proofs from the runtime binary, and the project pulls in no heavyweight
dependencies, leaving an `isqrt` executable well under a megabyte.

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
    [`Isqrt.Definitions.IsqrtIterative`](Isqrt/Definitions/IsqrtIterative.lean).
  - The definitions of the Python primitives: the Lean versions of Python's `>>`, `<<`
    and `//` operators, and the Lean versions of Python's `int.bit_length` and `range`.
    These definitions are all in
    [`Isqrt.Definitions.PythonPrimitives`](Isqrt/Definitions/PythonPrimitives.lean).
  - The exception-related definitions in
    [`Isqrt.Definitions.Exceptions`](Isqrt/Definitions/Exceptions.lean).
- The statements of correctness in
  [`Isqrt.Definitions.Specification`](Isqrt/Definitions/Specification.lean),
  in particular the `isCorrectIsqrt` predicate.
- That the `lake build` validation run includes validating the _proof_ of the
  correctness statement. That proof lives right at the bottom of
  [`Isqrt.Proofs.IterativeCorrectness`](Isqrt/Proofs/IterativeCorrectness.lean). The
  statement is simply: `theorem isCorrectIsqrt_isqrtIterative : isCorrectIsqrt
  isqrtIterative := ...`
- The Lean toolchain itself, including the compiler and standard library. It's
  conceivable (but highly unlikely) that Lean itself has bugs that mean that it reports
  validity of a proof that is actually invalid.

Notably, the proofs themselves do *not* need to be trusted. No matter how gnarly they
look, if Lean says that they're valid then they're valid.

So for this project, it's enough to read through and validate everything under
[`Isqrt.Definitions`](Isqrt/Definitions), along with the one-line statement (but not the
proof) of `isCorrectIsqrt_isqrtIterative` near the bottom of
[`Isqrt.Proofs.IterativeCorrectness`](Isqrt/Proofs/IterativeCorrectness.lean).
That's less than 250 lines of code total (including comments, docstrings and blank
lines). And in fact, some of those can be ignored: the `isCorrectIsqrt_isqrtIterative`
statement does not depend on the contents of
[`Isqrt.Definitions.IsqrtRecursive`](Isqrt/Definitions/IsqrtRecursive.lean), or on
the definition of `isNearSquareRoot` in
[`Isqrt.Definitions.Specification`](Isqrt/Definitions/Specification.lean).

For the correctness of the recursive version, similar comments apply: look at
[`Isqrt.Definitions`](Isqrt/Definitions) and the single-line statement (but not the
proof) of `isCorrectIsqrt_isqrtRecursive` in
[`Isqrt.Proofs.RecursiveCorrectness`](Isqrt/Proofs/RecursiveCorrectness.lean).

There are also empirical tests under [`Isqrt.Tests`](Isqrt/Tests), for particular chosen
input values. While these aren't formal proofs, they provide easy-to-read
empirical evidence that the two `isqrt` implementations do the right thing.

## Notes on the Python-to-Lean translation

A key goal of the Python-to-Lean translation is clear fidelity: the Lean translation
should be visibly equivalent to the original Python code, so that a reader can have
confidence that the two pieces of code are both representations of the same underlying
algorithm.

Lean 4's rich support for features resembling imperative programming - `do` notation,
mutable variables, `for` loops, exception handling - enables us to carry out a
remarkably faithful line-for-line translation of the Python code into Lean. Here's the
Lean translation of the main function:

```lean
/-- Return the integer part of the square root of the input. -/
def isqrtIterative (n : Int) : PyExcept Int := do
  if n < 0 then
    throw <| .valueError "isqrt() argument must be nonnegative"
  if n = 0 then
    return 0

  let c ← (n.bitLength - 1) // 2
  let mut a := 1
  let mut d := 0
  for s in List.reverse (range c.bitLength) do
    let e := d
    d ← c >> s
    a := (← a << d - e - 1) + (← (← n >> 2 * c - e - d + 1) // a)

  return if n < a * a then a - 1 else a
```

This section contains brief notes on some of the more interesting choices made for the
Lean translation.

### Case study: translating Python's floor division into Lean

Python's `//` operator, applied to two Python `int`s, returns the floor of the quotient
of those ints. Lean's `Int` type is a perfect match for Python's `int` (both represent
unbounded-precision integers), but Lean's standard division operator `/`, when applied
to two `Int`s, differs from Python's `//`:

- Both operators return an integer (`int` for Python, `Int` for Lean).
- For positive denominators, Lean's `/` and Python's `//` behave identically.
- For negative denominators, Lean's `/` returns the _ceiling_ of the quotient, while
  Python's `//` returns the floor.
- Most significantly, Lean's `/` operator returns `0` on division by zero, while
  Python's `//` raises a `ZeroDivisionError` on division by zero.

To translate Python's `//` into Lean, we have (at least) three choices:

- just use `/` (or `Int.fdiv`), and convince the reader that the difference doesn't
  matter because the algorithm never hits division by a nonpositive denominator anyway
- write our own Lean equivalent of Python's `//` that takes an extra argument, that
  extra argument being a *proof* that the denominator is nonzero
- write our own Lean equivalent of Python's `//` that returns _either_ the integer
  result in the case of a nonzero denominator, or a representation of an exception for
  the division by zero case.

The first is the weakest from a fidelity perspective, and it leaves a proof hole - we
might have Python code that _does_ (incorrectly) divide by zero in some unusual case,
but the "equivalent" Lean code might instead do the right thing as a result of
exercising the division-by-zero special case. Or we might be relying on division with a
negative denominator, where the semantics differ. So the Lean behaviour fails to be an
accurate reflection of the Python behaviour.

The second approach protects us from accidentally relying on Lean's division by zero
behaviour: a Python algorithm that hit division by zero would not be translatable into
Lean, because we wouldn't be able to manufacture the required proof argument for the
Lean version. But the need to supply those proof arguments at every call site makes it
harder to write the Lean translation, and it brings in visible divergence between the
Python code and its Lean translation, making it much harder for a reader to appreciate
the equivalence. It also leads to a tangling of proof and definitions.

The third approach gives us the high fidelity translation that we're after - we have a
Lean function whose behaviour is a very close match to Python's, and we get a clean
separation between function translations and proofs. The cost is that we now have to
thread the exception state through our algorithm. However, that cost turns out to be
low: Lean's syntactic sugar and elaborator support for monadic plumbing makes this
almost pain-free, at least on the definition side.

A previous proof attempt trialled the second approach; while it was successful, the
deviation between the two versions of the algorithm was significant. The current
proof instead uses the third approach.

Here's the Lean definition of the Python floor division that we use in this project:

```lean
def pyFloordiv (a b : Int) : PyExcept Int := do
  if b = 0 then throw <| .zeroDivisionError "division by zero"
  return Int.fdiv a b
```

Here `PyExcept` uses Lean's `Except` type: `PyExcept Int` represents the result of a
computation that _either_ returns an `Int` value or raises one of the two Python
exceptions that we care about. Here's the relevant code:

```lean
inductive PyException where
  | zeroDivisionError (msg : String)
  | valueError (msg : String)
  deriving Repr

abbrev PyExcept := Except PyException
```

As a final piece of syntactic sugar, in the modules that define the translated
`isqrt`, we define a local infix operator `//` that binds to `pyFloordiv`.

```lean
local infixl:70 "//" => pyFloordiv
```

That then lets us write `a // b` instead of `pyFloordiv a b`.

Analogous choices were made when translating Python's `<<` and `>>` operators, both of
which raise a `ValueError` on a negative shift count.

### The monadic tax

The starkest visible differences between the Python listing and its Lean equivalent
relate to Lean's plumbing for the imperative features present: exceptions, the for loop,
and mutable variables. That results in a zoo of assignment patterns on the Lean side
where Python uses only plain `=` assignment, and the use of the `←` prefix operator (a
_nested action_) _within_ some of the Lean expressions. A detailed discussion of these
features and the underlying monadic machinery is out of scope here; this section aims
to give a brief guide along with the appropriate searchable terminology for those who
want to know more.

Taking the oddities one by one, in the order that they appear in the code:

In normal Lean, a local definition is introduced using `let` syntax, for example in the
form `let x := some_expression`. So we might expect the translation of the Python line
`c = (n.bit_length() - 1) // 2` to be `let c := (n.bitLength - 1) // 2`. But that's not
quite right: we want `c` to have type `Int` in the following lines, and because `//` can
raise an exception, the type of `(n.bitLength - 1) // 2` is `PyExcept Int` instead. The
monadic let-binding `let c ← ...` (usable only within a `do` block) effectively allows
us to treat `c` as the unwrapped `Int` value within the rest of the `do` block, and
Lean's machinery takes care of surfacing any exception that occurred in the `//`.

The `let mut` bindings in the lines `let mut a := 1` and `let mut d := 0` introduce
local _mutable_ state (again restricted to the `do` block they're contained in). These
bindings let us mutate the values of `a` and `d` within the `for` loop. The underlying
mechanism Lean uses is similar to a state monad.

The `for` loop `for s in List.reverse (range c.bitLength) do` behaves as one might
expect, binding `s` to each element of the list in turn. Note that unlike Python,
`s` is in scope only within the body of the `for` loop.

The line `let e := d` is a normal `let` binding, creating a value for `e` that's local
to the `for` loop body. Note that we don't need `e` to be mutable: it's created anew
on each iteration of the `for` loop.

The line `d ← c >> s` updates the current value of the mutable state `d`. Note that
there's no `let` here, since we're not creating a new binding. A mutable state update
would normally be written `d := c >> s`, but we have the same issue here that we
encountered with the definition of `c`: `c >> s` has type `PyExcept Int`, and we want
`d` to have type `Int`. As before, the `←` form effectively unwraps that `PyExcept Int`
into an `Int`, propagating any exception through the rest of the computation.

The final line of the `for` loop,
`a := (← a << d - e - 1) + (← (← n >> 2 * c - e - d + 1) // a)`,
also introduces something new. As with `d`, we're updating the mutable state originally
introduced in the `let mut a := 1` line; this time the reassignment uses a regular `:=`
rather than the monadic `←`. But in the expression for the value being assigned we use
the prefix operator `←` (the _nested action_ form) to do local unwrappings of `PyExcept
Int` values into `Int`s. So for example `a << d - e - 1` has type `PyExcept Int`, but `←
a << d - e - 1` has type `Int`, with the Lean desugaring, elaboration and underlying
monadic machinery again taking care of propagating exceptions raised behind the scenes.

Note that the apparent asymmetry between the reassignments of `d` and `a` is merely
superficial: we could just as well have spelled the former assignment as
`d := (← c >> s)`.

For more background on these features of Lean, see the paper [*'do'
Unchained*][do-unchained], by Ullrich and de Moura. They're also described in the
"Functors, Monads and do-Notation" chapter of the Lean 4 reference manual.

### Equality: `=` vs `==`

> [!NOTE]
> **Lean details ahead.** A reader interested purely in the
> Python-fidelity story can skip this subsection — the short version is
> that the Lean test `if n = 0 then ...` has runtime behaviour
> identical to Python's `if n == 0:`. The rest of this subsection
> explains why, for readers who'd otherwise be suspicious of the `=`
> versus `==` mismatch.

Python's `==` takes two integers, compares them, and returns a Python
`bool`; that `bool` is then used by `if` to pick a branch. Lean has a
`==` operator that works similarly (returning something of type `Bool`),
but the equality tests in this project use `=` rather than `==`.
For an example,
see the line `if n = 0 then return 0` in `isqrtIterative`.

At first sight, this is a little odd: that `n = 0` expression here has type `Prop`, the
type of _propositions_ in Lean. In other words `n = 0` is a mathematical _assertion_
that `n` is zero, not a computational test.

However, Lean's `if-then` syntax requires more than just a `Prop`: it requires that
proposition to be *decidable*. A `Decidable` instance for a proposition `p` is,
concretely, one of two things: either a proof that `p` holds, or a proof that `¬p`
holds. (It's an inductive type with two constructors, `isTrue` and `isFalse`, each
carrying the corresponding proof — much like a `Bool` plus the matching proof.) Equality
between integers is decidable, so Lean supplies the procedure that constructs the
instance automatically, and the runtime semantics of the Lean function — ignoring the
proof layer — exactly match those of Python.

Note that `Int`-to-`Int` comparison (for example via `<`) is handled similarly: the
type of an expression like `n < 0` is `Prop`, but that expression remains usable in
`if` conditions because Lean manufactures a `Decidable` instance for it automatically.

### Bit length

Python's `int.bit_length()` is a _method_ on the `int` type that returns the number of
bits needed to represent `abs(n)`. For the Lean translation, we could have chosen to
write a plain old `bitLength : Int → Int` function. Instead, we define the Lean-side
function as `Int.bitLength` - it then lives in the `Int` namespace, and can be invoked
on a value `n` of type `Int` as `n.bitLength`, mirroring the Python method call
`n.bit_length()`. There's no real difference in utility, and a function would have
worked just as well, but the method call is cosmetically closer to the Python source.

### The correctness theorems

The correctness statement `isCorrectIsqrt` in
[`Isqrt.Definitions.Specification`](Isqrt/Definitions/Specification.lean) defines
what it means to be correct for an implementation of the integer square root function.
It's parameterised over the target function, allowing the same definition to be used
to assert correctness for both the iterative and recursive integer square root
implementations. Here's the proposition:

```lean
def isCorrectIsqrt (isqrt : Int → PyExcept Int) : Prop :=
  (∀ n, 0 ≤ n → ∃ a, returns (isqrt n) a ∧ isIntegerSquareRoot n a)
  ∧
  (∀ n, n < 0 → raises (isqrt n) (.valueError "isqrt() argument must be nonnegative"))
```

where `returns`, `raises` and `isIntegerSquareRoot` are defined by:

```lean
def returns {α : Type} (x : PyExcept α) (a : α) : Prop := x = .ok a
def raises {α : Type} (x : PyExcept α) (e : PyException) : Prop := x = .error e
def isIntegerSquareRoot (n a : Int) : Prop := 0 ≤ a ∧ a * a ≤ n ∧ n < (a + 1) * (a + 1)
```

In other words, `isCorrectIsqrt` represents the statement that, for a given
possibly-exception-raising function `isqrt` mapping integers to integers, that function
returns a correct integer square root for any nonnegative input, and raises a
`ValueError` with the expected message for any negative input. Note that this is simply
a statement, not a proof: for a given implementation of `isqrt`, the proposition
`isCorrectIsqrt isqrt` might be provable (in which case that implementation is proved
correct), or it might not.

The correctness theorems `isCorrectIsqrt_isqrtIterative` and
`isCorrectIsqrt_isqrtRecursive` provide proofs of the correctness statement
for the two implementations. By defining `isCorrectIsqrt` the way we have, the
_statements_ of those theorems become simple:

```lean
theorem isCorrectIsqrt_isqrtIterative : isCorrectIsqrt isqrtIterative := ...
theorem isCorrectIsqrt_isqrtRecursive : isCorrectIsqrt isqrtRecursive := ...
```


[batteries]: https://github.com/leanprover-community/batteries
[do-unchained]: https://lean-lang.org/papers/do.pdf
[elan]: https://github.com/leanprover/elan
[elan-installation]: https://github.com/leanprover/elan#installation
[integer-square-root]: https://en.wikipedia.org/wiki/Integer_square_root
[lean]: https://lean-lang.org
[math-integer-isqrt]: https://docs.python.org/3.15/library/math.integer.html#math.integer.isqrt
[math-integer-isqrt-github-current]: https://github.com/python/cpython/blob/v3.15.0b1/Modules/mathintegermodule.c#L191-L211
[math-isqrt-github-original]: https://github.com/python/cpython/blob/73934b9da07daefb203e7d26089e7486a1ce4fdf/Modules/mathmodule.c#L1515-L1535
[mathlib]: https://lean-lang.org/use-cases/mathlib/
