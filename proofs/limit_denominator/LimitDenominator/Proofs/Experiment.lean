module

public import LimitDenominator.Definitions.Specification
public import LimitDenominator.Proofs.Algorithm
public import LimitDenominator.Proofs.Arguments
public import LimitDenominator.Proofs.Candidate
public import LimitDenominator.Proofs.Uniqueness
import LimitDenominator.Proofs.BaseAnalysis
import LimitDenominator.Proofs.Reduced

/-!
The bridge from the proofs' vocabulary to the specification's.
-/

/-! # Post-loop analysis -/

/-
A `PostLoopState` is a `LoopState` whose loop condition has gone false. The loop's own
`r/s`, the *pure* candidate, and a second endpoint `t/u`, the *mixed* candidate built
from `p/q` and `r/s`, bracket the target fraction `m/n`. Both have denominator at most
`limit`, but `s + u > limit`, so everything strictly between them has denominator
exceeding `limit`: every candidate lies outside the bracket, or at one of its endpoints
(`lev_rs_or_tu_lev`).

The field `v` represents the orientation of the bracket, and from `bracket_det` it must
be either `1` or `-1`. If `v = 1` then we have

    r/s ≤ m/n < t/u

and if `v = -1` then we have

    t/u < m/n ≤ r/s

`rs_lev_mn` and `mn_lev_tu` state this, in the non-strict form the later proofs use.
-/

namespace PostLoopState

/- We fix a post-loop state `st` throughout this section. -/
variable {args : Arguments} (st : PostLoopState args)

/-! ## Orientation-aware order -/

/- Generic candidates. -/
variable (ef gh : Candidate args)

/-! ## The determinant -/

/-! ## Residuals -/

/-! ## Recovering the target -/

/-! ## Distances -/

/-! ## The bracket -/

/-! ## Best approximations -/

variable {yz : Candidate args}

/-! ## Choosing between the two candidates -/

/-! ## The ambiguous case -/


end PostLoopState

namespace Arguments

variable (args : Arguments)

/-! # Results -/

/-! ## Uniqueness of best approximations -/

/-! ## Any best approximation is reduced -/

/-! ## The trivial case -/

/-! ## The return value -/

end Arguments

/-! ## The residual stays positive -/

/-! # The specification -/

/-
Everything above is in the proofs' own vocabulary. This section is where it meets the
specification's, and the only part of the file that mentions `isBestApproximation`.
-/

/--
`best` and `isBestApproximation` say the same thing of the same pair: `better` and
`isBetterApproximation` are the same formula.
-/
public theorem best_iff_isBestApproximation {args : Arguments} (ef : Candidate args) :
    ef.best ↔ isBestApproximation args.m args.n args.limit ef.num ef.den :=
  ⟨fun hbest => ⟨ef.den_pos, ef.den_limited, fun y z h => hbest ⟨y, z, h.1, h.2⟩⟩,
    fun ⟨_, _, hall⟩ gh => hall gh.num gh.den ⟨gh.den_pos, gh.den_limited⟩⟩

/-- `Arguments.ambiguous` is the specification's `isAmbiguous`, formula for formula. -/
public theorem ambiguous_iff_isAmbiguous (args : Arguments) :
    args.ambiguous ↔ isAmbiguous args.m args.n args.limit := Iff.rfl

/-- The algorithm's answer satisfies the specification. -/
public theorem Arguments.isBestApproximation_limitDenominator (args : Arguments) :
    isBestApproximation args.m args.n args.limit
      args.limitDenominator.num args.limitDenominator.den :=
  (best_iff_isBestApproximation _).mp args.limitDenominator_best

/-- In the specification's ambiguous case, the algorithm's answer is `(m / n, 1)`. -/
public theorem Arguments.limitDenominator_eq_of_isAmbiguous (args : Arguments)
    (hamb : isAmbiguous args.m args.n args.limit) :
    (args.limitDenominator.num, args.limitDenominator.den) = (args.m / args.n, 1) := by
  rw [args.limitDenominator_ambiguous_case ((ambiguous_iff_isAmbiguous args).mpr hamb)]
  rfl

/--
Outside the ambiguous case the specification determines the answer: no two distinct
pairs satisfy it.
-/
public theorem isBestApproximation_unique_of_not_ambiguous {m n l r₁ s₁ r₂ s₂ : Int}
    (hn : 0 < n) (hamb : ¬ isAmbiguous m n l)
    (h₁ : isBestApproximation m n l r₁ s₁) (h₂ : isBestApproximation m n l r₂ s₂) :
    r₁ = r₂ ∧ s₁ = s₂ := by
  have hl : 1 ≤ l := by have := h₁.1; have := h₁.2.1; omega
  let args : Arguments := ⟨m, n, l, hn, hl⟩
  let ef : Candidate args := ⟨r₁, s₁, h₁.1, h₁.2.1⟩
  let gh : Candidate args := ⟨r₂, s₂, h₂.1, h₂.2.1⟩
  have heq : ef = gh :=
    args.non_ambiguous_best (fun ha => hamb ((ambiguous_iff_isAmbiguous args).mp ha))
      ((best_iff_isBestApproximation ef).mpr h₁)
      ((best_iff_isBestApproximation gh).mpr h₂)
  exact ⟨congrArg Candidate.num heq, congrArg Candidate.den heq⟩

/--
In the ambiguous case the specification is satisfied by exactly two pairs, the floor and
the floor plus one, each over denominator one.
-/
public theorem isBestApproximation_iff_of_ambiguous {m n l r s : Int}
    (hn : 0 < n) (hamb : isAmbiguous m n l) :
    isBestApproximation m n l r s ↔ (r, s) = (m / n, 1) ∨ (r, s) = (m / n + 1, 1) := by
  have hl : 1 ≤ l := by have := hamb.1; omega
  let args : Arguments := ⟨m, n, l, hn, hl⟩
  constructor
  · intro h
    have := (args.ambiguous_best hamb).mp
      ((best_iff_isBestApproximation ⟨r, s, h.1, h.2.1⟩).mpr h)
    grind only [Arguments.floor, Arguments.floorAddOne]
  · intro h
    have hfloor := (best_iff_isBestApproximation args.floor).mp
      ((args.ambiguous_best hamb).mpr (Or.inl rfl))
    have hadd := (best_iff_isBestApproximation args.floorAddOne).mp
      ((args.ambiguous_best hamb).mpr (Or.inr rfl))
    grind only [Arguments.floor, Arguments.floorAddOne]

/--
The result is reduced, and that is a consequence of the specification rather
than a part of it.

A pair satisfying the specification is one of the two bracket endpoints, and the
bracket's determinant is a Bézout identity for each of them.
-/
public theorem isBestApproximation.gcd_eq_one {m n l r s : Int} (hn : 0 < n)
    (h : isBestApproximation m n l r s) : Int.gcd r s = 1 := by
  have hl : 1 ≤ l := by have := h.1; have := h.2.1; omega
  let args : Arguments := ⟨m, n, l, hn, hl⟩
  let ef : Candidate args := ⟨r, s, h.1, h.2.1⟩
  exact args.reduced_of_best ((best_iff_isBestApproximation ef).mpr h)
