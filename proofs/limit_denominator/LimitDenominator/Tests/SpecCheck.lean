module

public import LimitDenominator.Definitions.Specification

/-!
A `Bool`-valued, bounded form of `isBestApproximation`, and the grid of targets it is checked
over.

The test vectors in `LimitDenominator.Tests.Vectors` compare against expected values, which
barely exercises a specification whose substance is a `∀`-quantified optimality condition. This
file checks the specification itself, by evaluating it.
-/

@[expose] public section

/-- `Bool`-valued form of `atLeastAsClose`. -/
def checkAtLeastAsClose (m n r s y z : Int) : Bool :=
  (r * n - m * s).abs * z ≤ (y * n - m * z).abs * s

/-- `Bool`-valued form of the two clauses `isBestApproximation` asserts of one candidate. -/
def checkCandidate (m n r s y z : Int) : Bool :=
  checkAtLeastAsClose m n r s y z
  && (!checkAtLeastAsClose m n y z r s || s ≤ z)

/--
`Bool`-valued form of `isAmbiguous`: the limit is one and `2 * m / n` is an odd integer.

Both readings of `%` want `0 < n`, which the grid below supplies. Given that, `%` on `Int`
being `emod`, the divisibility test and the odd-quotient test are both right for either sign
of `m`.
-/
def checkAmbiguous (m n l : Int) : Bool :=
  l == 1 && 2 * m % n == 0 && (2 * m / n) % 2 == 1

/--
`Bool`-valued bounded form of `isBestApproximation`.

`isBestApproximation` quantifies over every candidate `(y, z)` with `0 < z ≤ l`. The `z` are
bounded, so those are enumerated; the `y` are not, so for each `z` only the two integers
bracketing `m * z / n` are checked.

Both of those steps need `0 < n`, which the grid supplies: it is what makes `m * z / n` the
floor, Lean's `Int` division agreeing with the floor only for a positive divisor, and it is
what confines `m * z % n` to `[0, n)` below. Given that, the two `y` suffice:

* `|y*n - m*z|` is smallest at those two `y`, taking the values `t` and `n - t` where
  `t = m*z % n`, and every other `y` gives at least `n + min(t, n - t)`.
* So if the closeness clause holds at whichever of the two is nearer, then for every other `y`
  it holds *strictly*.
* The tie-break clause is conditioned on the closeness inequality holding in reverse, so
  wherever the closeness clause holds strictly it is vacuous.

Two conjuncts below go beyond `isBestApproximation`, deliberately, and both are checks on
statements the proof layer makes about the specification rather than within it. `Int.gcd r s
== 1` is an independent empirical check of `isBestApproximation.gcd_eq_one`, which derives
lowest terms from the two clauses instead. The ambiguous-case conjunct pins the choice the
specification leaves open: where two pairs satisfy it, the one returned is the floor.
-/
def checkBestApproximation (m n l r s : Int) : Bool :=
  0 < s && s ≤ l && Int.gcd r s == 1
  && (!checkAmbiguous m n l || (r == m / n && s == 1))
  && (List.range l.toNat).all fun i =>
    let z : Int := i + 1
    let y : Int := m * z / n
    checkCandidate m n r s y z && checkCandidate m n r s (y + 1) z

/--
Targets and denominator limits for the specification check: every `m / n` with `1 ≤ n ≤ 16` and
`-32 ≤ m ≤ 32`, against every limit `1 ≤ l ≤ 12`.
-/
def specCheckGrid : List (Int × Int × Int) :=
  (List.range 16).flatMap fun (i : Nat) =>
    (List.range 65).flatMap fun (j : Nat) =>
      (List.range 12).map fun (k : Nat) =>
        ((j : Int) - 32, (i : Int) + 1, (k : Int) + 1)

end
