module

public import LimitDenominator.Definitions.IntAbs
public import LimitDenominator.Proofs.Arguments
import LimitDenominator.Proofs.IntLemmas

/-!
Candidate solutions to the problem, and the ordering on them: when one candidate is
*better* than another, and what it means for a candidate to be *best*.
-/

/--
A *candidate* solution to the problem is a (possibly non-reduced) fraction `num / den`
whose denominator is positive and bounded by the given limit.
-/
public structure Candidate (args : Arguments) where
  /-- Numerator of the candidate fraction. -/
  num : Int
  /-- Denominator of the candidate fraction. -/
  den : Int
  den_pos : 0 < den
  den_limited : den ≤ args.limit

namespace Candidate

variable {args : Arguments}

/-- A candidate is *reduced* if its numerator and denominator are coprime. -/
@[expose] public def isReduced (ef : Candidate args) :=
  ∃ (g h : Int), g * ef.num + h * ef.den = 1

/-- Two candidates that are numerically equal and have equal denominator are equal. -/
public theorem eq_of_den_eq_of_cross_eq {ef gh : Candidate args}
    (h_deneq : ef.den = gh.den) (heq : ef.num * gh.den = gh.num * ef.den) :
    ef = gh := by
  rw [Candidate.mk.injEq]
  exact ⟨Int.eq_of_eq_mul_pos gh.den_pos (h_deneq ▸ heq), h_deneq⟩

/-
Given candidates `e/f` and `g/h`, we say that `e/f` is *better* than `g/h` if either:

- `e/f` is closer to `m/n` than `g/h` is, or
- `e/f` and `g/h` are equidistant from `m/n` and `f ≤ h`.

Note the slight abuse of language: "better" suggests a non-reflexive relation, but
our "better" relation is reflexive: `e/f` is better than itself.

A *best* candidate is then a candidate that's better than any other candidate.
-/

/-- Absolute distance from `m/n` to `e/f`, scaled by both denominators. -/
@[expose] public def dist (ef : Candidate args) : Int :=
  (ef.num * args.n - args.m * ef.den).abs

/-- Definition of the *better* relation. -/
@[expose] public def better (ef gh : Candidate args) :=
  ef.dist * gh.den < gh.dist * ef.den
  ∨
  ef.dist * gh.den = gh.dist * ef.den ∧ ef.den ≤ gh.den

/-- Definition of *best*. -/
@[expose] public def best (ef : Candidate args) := ∀ (gh : Candidate args), ef.better gh

/-- The `better` relation is transitive. -/
public theorem better_trans {ef gh ij : Candidate args} (h1 : ef.better gh)
    (h2 : gh.better ij) : ef.better ij := by
  rcases h1 with h1 | ⟨h1, d1⟩ <;> rcases h2 with h2 | ⟨h2, d2⟩
  · left; exact Int.lt_of_lt_mul_pos gh.den_pos
      (by grind only [Int.lt_mul_pos ij.den_pos h1, Int.lt_mul_pos ef.den_pos h2])
  · left; exact Int.lt_of_lt_mul_pos gh.den_pos
      (by grind only [Int.lt_mul_pos ij.den_pos h1, Int.eq_mul_pos ef.den_pos h2])
  · left; exact Int.lt_of_lt_mul_pos gh.den_pos
      (by grind only [Int.eq_mul_pos ij.den_pos h1, Int.lt_mul_pos ef.den_pos h2])
  · right
    exact ⟨Int.eq_of_eq_mul_pos gh.den_pos
        (by grind only [Int.eq_mul_pos ij.den_pos h1, Int.eq_mul_pos ef.den_pos h2]),
      Int.le_trans d1 d2⟩

end Candidate

namespace Arguments

/-- `⌊m/n⌋` as a candidate. -/
@[expose] public def floor (args : Arguments) : Candidate args :=
  ⟨args.m / args.n, 1, by decide, args.one_le_limit⟩

/-- `⌊m/n⌋ + 1` as a candidate. -/
@[expose] public def floorAddOne (args : Arguments) : Candidate args :=
  ⟨args.m / args.n + 1, 1, by decide, args.one_le_limit⟩

end Arguments
