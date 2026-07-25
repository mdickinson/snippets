# Plan: Lean 4 correctness proof for `Fraction.limit_denominator`

Working plan for a Lean 4 project under `proofs/limit_denominator`, formalising the
informal correctness proof in [python/cpython#95723][issue], in the style of
[`proofs/isqrt`](../isqrt): high-fidelity Python-to-Lean translation using Lean's
monadic support for imperative features, with exception-raising Python primitives.

Terminology is fixed in [CONTEXT.md](CONTEXT.md). This file and CONTEXT.md are planning
scaffolding, to be folded into README.md and PROOF.md as the project settles.

## Deliverables

Branch `limit-denominator`, off current `main`. Two PRs:

**PR 1 — the simplified listing.** Complete and self-contained: Python primitives, the
translation, the specification, the correctness proof, tests, README.md, PROOF.md, CI
workflow. Reviewable alone, and worth landing even if PR 2 never does.

**PR 2 — the stdlib listing.** Adds `limitDenominatorStdlib`, its loop mechanics, and the
argument (issue § "Optimization") that the `0 < b` check is unnecessary for reduced
targets with `l < n`. Extends PROOF.md and the README trust section to cover both.

## Toolchain findings this plan depends on

All verified against `leanprover/lean4:v4.32.1`, the toolchain `proofs/isqrt` pins.

1. **Python's `while` translates to Lean's `while`.** `while` elaborates to
   `Lean.Loop.forIn`, which is built on a `partial def` — but 4.32 ships
   `Lean.Loop.forIn_eq_of_monadTail`, a one-step unfolding lemma for any monad with a
   `Lean.Order.MonadTail` instance, and `Except ε` has one (`Init.Internal.Order.While`).
   A reusable measure-plus-invariant lemma over `while` was written and used to prove a
   concrete loop end to end. No fuel parameter and no recursive-helper rewrite needed.

2. **Lean's `while` condition does not short-circuit.** A `←` nested action inside the
   condition is hoisted *before* the whole condition, so a naive translation of
   `while 0 < b and q + a // b * s <= l` raises `ZeroDivisionError` exactly where Python
   exits cleanly. Hence `pyAnd` (below).

3. **No notation can spell `pyAnd`.** The do-elaborator harvests `←` from the
   *unexpanded* syntax tree, so a macro that wraps its operand in `do` arrives too late —
   confirmed, including with the operands fully parenthesised. Worse, it compiles and
   silently gets the semantics wrong. `pyAnd` must be applied by name, with the delayed
   operand written as an explicit `do` block at the call site.

4. **Simultaneous tuple assignment works.** Both `let mut (a, b, p, q, r, s) := …` and
   six-way reassignment `(a, b, p, q, r, s) := …` elaborate, so Python's tuple assignment
   translates directly. This matters: the loop body's updates are genuinely simultaneous.

5. **`Int.fdiv`/`Int.fmod` match Python's `//`/`%`** on every combination of signs
   (checked against CPython), and `Int.gcd` matches `math.gcd`.

6. **Every divisor in the algorithm is positive**, and
   `Int.fdiv_eq_ediv_of_nonneg`/`Int.fmod_eq_emod_of_nonneg` condition on the *divisor*.
   So the proof layer works entirely in Euclidean `/` and `%` after one bridge per
   primitive, exactly as isqrt's proof layer does — no `fdiv` in the proofs.

7. **`grind` does the nonlinear integer algebra.** The derived invariants
   `(pn − mq)v = a` and `(ms − rn)v = b`, and the bracket identity
   `z = (tz − yu)v·s + (ys − rz)v·u`, all close with `grind` after substitution. This was
   the main feasibility risk for the math layer, since `ring` and `linarith` are Mathlib.

8. **`|·|` is not in core** (it comes from Mathlib's order hierarchy), so the spec defines
   a one-line `Int.abs`. `Rat` *is* in core but its lemma API is thin; not used.

9. **The coprimality step is short.** `gcd_eq_one_of_det` — a unit determinant against any
   other pair implies coprimality — is proved from `Int.gcd_dvd_left`/`_right` plus
   `Nat.dvd_one` in about eight lines. Verified.

## Settled decisions

| Decision | Choice | Why |
| --- | --- | --- |
| Target code | Both listings, simplified first | Closes the gap between proved code and shipped code; the simplified one is what the informal proof matches |
| Python's `and` | Model as a `pyAnd` primitive | Keeps the exit test in one expression at the top of the loop; consistent with modelling `//` and `%` rather than dodging their semantics |
| Orientation `v` | Dropped from the definitions | Nothing inert in the trusted surface; and it costs nothing, being a derived quantity (below) |
| Spec content | Closest **and** both tie-breaks | Complete functional characterisation, as `isIntegerSquareRoot` is for isqrt; all three are CPython documented promises |
| Absolute value | One-line `Int.abs` | Statement clarity in the trusted surface, over avoiding a definition |
| Preconditions | A `valid` parameter on the spec | One spec, two one-line theorems; each listing's precondition visible in its own theorem |
| Proof prose | A dedicated PROOF.md | The durable home the issue wanted; keeps README focused on translation and trust |
| Tests | Vectors + executable spec check | Vectors barely exercise a ∀-quantified optimality condition |
| Primitives | Duplicated from isqrt, not shared | Each project stands alone; sharing would need a third package and break self-containedness |

### The orientation is derived, not extra state

The invariant gives `(ps − rq)v = 1` with `v = ±1`. Multiplying by `v` gives `v = ps − rq`.
So the orientation is a *function of the state*, and the invariant clause is just
`p*s − r*q = 1 ∨ p*s − r*q = −1`. No existential, no extra variable. Verified numerically:
for `m, n = 6, 4` the state runs `v = 1` then `v = −1`, alternating as the issue says.

### Consequence: our Python listing is not verbatim from the issue

Dropping `v` means the Python listing shown in README.md/PROOF.md must drop it too, or the
line-for-line correspondence breaks. So the listing we present differs from the issue's by
the removal of `v`. The README should say so plainly. Note this partly undercuts the
reason for choosing `pyAnd` (keeping the listing verbatim) — `pyAnd` still earns its place
on the "model Python's semantics rather than dodge them" argument, but not on verbatimness.

## The translation (PR 1)

Python, adapted from the issue's § "Set-up" by removing `v`:

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

Lean — this elaborates and gives the right answer on every docstring example plus the
unreduced, halfway, negative and `ValueError` cases:

```lean
/-- Closest fraction to `m / n` with denominator at most `l`, as a numerator/denominator pair. -/
def limitDenominatorSimplified (m n l : Int) : PyExcept (Int × Int) := do
  if l < 1 then
    throw <| .valueError "max_denominator should be at least 1"

  let mut (a, b, p, q, r, s) := (n, ← m % n, 1, 0, ← m // n, 1)
  while ← pyAnd (0 < b) (do return q + (← a // b) * s ≤ l) do
    (a, b, p, q, r, s) := (b, ← a % b, r, s, p + (← a // b) * r, q + (← a // b) * s)
  let (t, u) := (p + (← (l - q) // s) * r, q + (← (l - q) // s) * s)
  return if 2 * b * u ≤ n then (r, s) else (t, u)
```

Primitives:

```lean
/-- The floor of `a / b`, raising `zeroDivisionError` if `b` is zero. -/
def pyFloordiv (a b : Int) : PyExcept Int := do
  if b = 0 then throw <| .zeroDivisionError "division by zero"
  return Int.fdiv a b

/-- Equivalent of Python's `a % b`, raising `zeroDivisionError` if `b` is zero. -/
def pyMod (a b : Int) : PyExcept Int := do
  if b = 0 then throw <| .zeroDivisionError "division by zero"
  return Int.fmod a b

/--
Python's short-circuiting `and`, for boolean operands. Python always evaluates the left
operand, so only the right one is delayed.
-/
def pyAnd (x : Bool) (y : PyExcept Bool) : PyExcept Bool := do
  if x then y else return false
```

with scoped `infixl:70` notation for `//` and `%` at Python's precedence.

## The specification

```lean
/-- Absolute value of an integer. -/
def Int.abs (a : Int) : Int := if 0 ≤ a then a else -a

/--
`(r, s)` is at least as close to `m / n` as `(y, z)` is, for positive denominators `s` and
`z`. Both sides of `|m/n - r/s| ≤ |m/n - y/z|` are scaled by the positive quantity
`n * s * z`.
-/
def atLeastAsClose (m n r s y z : Int) : Prop :=
  (m * s - r * n).abs * z ≤ (m * z - y * n).abs * s

/--
What it means for `r / s` to be the best approximation to `m / n` with denominator at most
`l`: closest, with ties broken towards the smaller denominator and any remaining tie
towards the smaller fraction, in lowest terms.
-/
def isBestApproximation (m n l r s : Int) : Prop :=
  0 < s ∧ s ≤ l ∧ Int.gcd r s = 1 ∧
  ∀ y z : Int, 0 < z → z ≤ l →
    atLeastAsClose m n r s y z
    ∧ (atLeastAsClose m n y z r s → s ≤ z)
    ∧ (atLeastAsClose m n y z r s → s = z → r ≤ y)

/--
Statement that a function has the correct behaviour on `valid` targets: raises a
`valueError` with the expected message when the denominator limit is less than one, and
otherwise returns the best approximation.
-/
def isCorrectLimitDenominator
    (valid : Int → Int → Prop)
    (limitDenominator : Int → Int → Int → PyExcept (Int × Int)) :=
  (∀ {m n l : Int}, l < 1 →
      raises (limitDenominator m n l) (.valueError "max_denominator should be at least 1"))
  ∧
  (∀ {m n l : Int}, valid m n → 1 ≤ l →
      ∃ r s, returns (limitDenominator m n l) (r, s) ∧ isBestApproximation m n l r s)
```

The two headline theorems:

```lean
theorem isCorrectLimitDenominator_simplified :
    isCorrectLimitDenominator (fun _ n => 0 < n) limitDenominatorSimplified

theorem isCorrectLimitDenominator_stdlib :
    isCorrectLimitDenominator (fun m n => 0 < n ∧ Int.gcd m n = 1) limitDenominatorStdlib
```

Note `n ≤ 0` is deliberately unspecified: Python cannot produce such a target, since a
`Fraction`'s denominator is always positive.

## Proof architecture

Organising principle inherited from isqrt: separate the **mechanics** (unravelling the
`do` block, threading `.ok`, bridging Python's division to Euclidean division, driving the
loop) from the **math** (invariants, the bracket, tie-breaking), and let the module
structure mirror the split.

```
LimitDenominator/
├── Definitions/
│   ├── Exceptions.lean                  PyException, PyExcept
│   ├── PythonPrimitives.lean            pyFloordiv, pyMod, pyAnd, notation
│   ├── LimitDenominatorSimplified.lean  the translation
│   ├── LimitDenominatorStdlib.lean      PR 2
│   └── Specification.lean               Int.abs, atLeastAsClose,
│                                        isBestApproximation, isCorrectLimitDenominator
├── Proofs/
│   ├── SupportLemmas.lean               general Int facts core lacks; Int.abs lemmas;
│   │                                    gcd_eq_one_of_det; floor characterisations
│   ├── WhileLoop.lean                   forIn_loop_eq, forIn_loop_invariant (generic)
│   ├── PythonTranslation.lean           pyFloordiv/pyMod/pyAnd → Euclidean bind helpers
│   ├── LoopInvariant.lean               LoopInvariant, _initial, _step, derived residuals
│   ├── AfterLoop.lean                   k, t, u, c and their identities and bounds
│   ├── Bracket.lean                     the key lemma; candidates outside the bracket
│   ├── TieBreak.lean                    the two tie-break sections
│   ├── SimplifiedCorrectness.lean       assembles isCorrectLimitDenominator_simplified
│   └── StdlibCorrectness.lean           PR 2
└── Tests/
    ├── Assertions.lean                  assertReturns / assertRaisesValueError
    ├── Vectors.lean                     docstring examples and edge cases
    ├── SpecCheck.lean                   checkBestApproximation, the grids
    └── LimitDenominator{Simplified,Stdlib}.lean
```

### Mechanics: driving the loop

Generic, monad-agnostic, in `WhileLoop.lean`; verified working:

```lean
theorem forIn_loop_invariant
    {m : Type → Type} {α : Type} [Monad m] [LawfulMonad m] [Lean.Order.MonadTail m]
    (measure : α → Nat)
    (body : Unit → α → m (ForInStep α))
    (invariant post : α → Prop)
    (hstep : ∀ r, invariant r →
      (∃ r', body () r = pure (ForInStep.yield r') ∧ invariant r' ∧ measure r' < measure r) ∨
      (∃ r', body () r = pure (ForInStep.done r') ∧ post r'))
    (r : α) (hr : invariant r) :
    ∃ y, forIn Lean.Loop.mk r body = pure y ∧ post y
```

The measure is `b.toNat`, decreasing because the new `b` is `a % b` with `0 < b`. The
`post` supplied at the call site is `invariant ∧ (b ≤ 0 ∨ l < q + (a / b) * s)` — the
invariant plus the negation of the loop condition. The six-tuple appears only here; the
math layer takes six `Int` arguments and never projects out of a tuple.

### Math: the invariant

Transcribing the issue's § "Details: loop invariants", with `v = p*s − r*q`:

```lean
/-- The invariant holding before the loop and after every iteration. -/
structure LoopInvariant (m n l a b p q r s : Int) : Prop where
  det : p * s - r * q = 1 ∨ p * s - r * q = -1
  numerator : a * r + b * p = m
  denominator : a * s + b * q = n
  b_nonneg : 0 ≤ b
  b_lt_a : b < a
  q_nonneg : 0 ≤ q
  q_le_s : q ≤ s
  s_le_l : s ≤ l
  s_pos : 0 < s
```

with `loopInvariant_initial`, `loopInvariant_step`, and the derived residuals
`(p*n − m*q)*v = a` and `(m*s − r*n)*v = b` (both `grind`-provable after substitution).

The residuals are what make the absolute values in the spec disappear on the algorithm's
side: `|m*s − r*n| = b` and `|t*n − m*u| = c`, so `atLeastAsClose` against the returned
pair reduces to `b * z ≤ |m*z − y*n| * s`, with the only surviving `abs` on the candidate.

### Math: after the loop, the bracket, tie-breaking

Following the issue section by section — § "Details: after the loop" gives `k`, `t`, `u`,
`c`, the four identities, `u ≤ l < u + s`, `b ≤ c` and `0 < c`; § "Proof overview" gives
the bracket lemma; the two § "Tie-breaking" sections give the final comparison.

Final assembly, for a candidate `(y, z)` with `0 < z ≤ l`:

1. The bracket lemma: no candidate lies strictly between the loop candidate and the
   extended candidate. So `y/z` is on one side or the other.
2. On the loop candidate's side, `y/z` is at least as far as the loop candidate; on the
   extended candidate's side, at least as far as the extended candidate. Either way it is
   at least as far as the *nearer* of the two.
3. `2*b*u ≤ n ↔ b*u ≤ c*s` says the returned pair is the nearer of the two.
4. Tie-break clause 2: equality forces `y/z` to equal one of the two candidates as a
   *value*; coprimality then gives divisibility of `z` by that denominator, hence the
   inequality — together with `s ≤ u` on a tie, from § "Tie-breaking, part I".
5. Tie-break clause 3 is § "Tie-breaking, part II": `s = z` forces `l = 1`, `q = 0` and
   zero loop iterations, whence `t = r + 1` and the returned pair is the lower bound.

## Tests

```lean
#guard limitDenominatorCases.all fun (m, n, l, r, s) =>
  assertReturns (limitDenominatorSimplified m n l) (r, s)

#guard grid.all fun (m, n, l) =>
  match limitDenominatorSimplified m n l with
  | .ok (r, s) => checkBestApproximation m n l r s
  | .error _ => false
```

`checkBestApproximation` is a `Bool`-valued bounded form of `isBestApproximation`:
exhaustive over `z` in `1 … l`, and over `y` it checks the two values bracketing
`m * z / n`, which suffices because any other `y` satisfies the closeness clause trivially
and the tie-break clauses vacuously. That argument goes in a comment at the definition.

Vectors: the three docstring examples, an unreduced target, a halfway target and its
negative, an integer target, `l = 1`, and the `ValueError`. PR 2 adds a grid cross-check
`limitDenominatorStdlib m n l == limitDenominatorSimplified m n l` on reduced targets.

Independently of Lean, the simplified listing was differential-tested against
`Fraction.limit_denominator` in Python over 150,696 cases (`n` in 1…39, `m` in −80…80,
`l` in 1…24) with no mismatches, and with `gcd(r, s) = 1` and `0 < s ≤ l` asserted
throughout. Worth repeating and recording when PR 1 lands.

## Scaffolding

Mirrors `proofs/isqrt` throughout: Lean's module system (`module`, `public import`,
`@[expose] public section`), `lean-toolchain` at `leanprover/lean4:v4.32.1`, Batteries
`v4.32.0` required solely for `lintDriver = "batteries/runLinter"`, `autoImplicit = false`,
Mathlib-free.

- Package `limit_denominator`; libs `LimitDenominator` and `LimitDenominatorTests`; exe
  `limit_denominator` rooted at `Main.lean`.
- A CLI taking `m n l` and printing `r/s`, which — as isqrt's does — leans on the
  correctness proof to omit handling for the impossible exception case. **Proposed, not
  yet agreed.**
- CI: `.github/workflows/lean-limit-denominator.yml`, a copy of `lean-isqrt.yml` with the
  paths and `lake-package-directory` changed. Same triggers: pushes to main and pull
  requests, both path-filtered, plus `workflow_dispatch`.

Conventions carried over from the isqrt proof layer without re-litigation: Mathlib theorem
naming; camelCase `def`/`structure` names with docstrings, and `@[inherit_doc]` on
notation, for `lake lint`; Python listings keep `snake_case`; spec definitions fold their
defining sign conditions in as leading conjuncts while theorems minimise hypotheses;
`Int`/`Nat` spelled out except in genuine math prose; `Nat` for indices and `Int` for
values, with `Definitions/` all-`Int`; casts rather than `toNat` in statements; `/-! -/`
module docs after the imports in every file; single-line `/-- -/` docstrings, multiline
always block style; lines ≤ 100 characters; a space after `←` in rewrites; Loogle checks
before stating any general `Int`/`Nat` lemma.

## Risks and open items

- **`Int.abs` in the proofs.** The spec is stated with `Int.abs`, but `omega` only knows
  `Int.natAbs`. Mitigation: `Int.abs_eq_natAbs` (proved by `omega`) rewritten once at the
  boundary; and the residual identities remove `abs` from the algorithm's side entirely.
- **`grind` on the bigger algebraic steps.** It handled the four identities tested, but
  the bracket assembly and tie-break comparisons are larger. If `grind` stalls, the
  fallback is explicit `calc` chains with `Int.mul_le_mul` and friends — slower to write,
  no new risk. Worth probing the largest step early rather than late.
- **PR 2's mechanics are genuinely different.** `while True` with a mid-loop `break` means
  the body's exit is a `ForInStep.done` from the middle rather than a false condition at
  the top; `forIn_loop_invariant` already covers that shape, but the fold onto the
  desugared body will need its own `loopBody`-style bridge.
- **Unspecified `n ≤ 0`.** Deliberate, but worth a sentence in the README so it doesn't
  read as an oversight.
- **CLI** is proposed, not agreed.

[issue]: https://github.com/python/cpython/issues/95723
