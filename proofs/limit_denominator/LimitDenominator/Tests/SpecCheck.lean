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
  (m * s - r * n).abs * z ≤ (m * z - y * n).abs * s

/-- `Bool`-valued form of the three clauses `isBestApproximation` asserts of one candidate. -/
def checkCandidate (m n r s y z : Int) : Bool :=
  checkAtLeastAsClose m n r s y z
  && (!checkAtLeastAsClose m n y z r s || s ≤ z)
  && (!checkAtLeastAsClose m n y z r s || s ≠ z || r ≤ y)

/--
`Bool`-valued bounded form of `isBestApproximation`.

`isBestApproximation` quantifies over every candidate `(y, z)` with `0 < z ≤ l`. The `z` are
bounded, so those are enumerated; the `y` are not, so for each `z` only the two integers
bracketing `m * z / n` are checked.

Both of those steps need `0 < n`, which the grid supplies: it is what makes `m * z / n` the
floor, Lean's `Int` division agreeing with the floor only for a positive divisor, and it is
what confines `m * z % n` to `[0, n)` below. Given that, the two `y` suffice:

* `|m*z - y*n|` is smallest at those two `y`, taking the values `t` and `n - t` where
  `t = m*z % n`, and every other `y` gives at least `n + min(t, n - t)`.
* So if the closeness clause holds at whichever of the two is nearer, then for every other `y`
  it holds *strictly*.
* The two tie-break clauses are conditioned on the closeness inequality holding in reverse, so
  wherever the closeness clause holds strictly they are vacuous.
-/
def checkBestApproximation (m n l r s : Int) : Bool :=
  0 < s && s ≤ l && Int.gcd r s == 1
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
