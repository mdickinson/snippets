module

public import LimitDenominator.Proofs.Algorithm
public import LimitDenominator.Proofs.Candidate
import LimitDenominator.Proofs.IntLemmas
import LimitDenominator.Proofs.Optimality

/-!
Reduced candidates, and the proof that both bracket endpoints, and hence any best
approximation, are reduced.
-/

/-- A candidate is *reduced* if its numerator and denominator are coprime. -/
@[expose] public def Candidate.reduced {args : Arguments} (ef : Candidate args) :=
  Int.gcd ef.num ef.den = 1

namespace PostLoopState

/-- The pure candidate `r/s` is reduced. -/
theorem reduced_rs {args : Arguments} (st : PostLoopState args) : st.rs.reduced :=
  Int.gcd_eq_one_of_bezout (g := -st.u * st.v) (h := st.t * st.v)
    (by grind only [st.bracket_det])

/-- The mixed candidate `t/u` likewise. -/
theorem reduced_tu {args : Arguments} (st : PostLoopState args) : st.tu.reduced :=
  Int.gcd_eq_one_of_bezout (g := st.s * st.v) (h := -st.r * st.v)
    (by grind only [st.bracket_det])

end PostLoopState

/--
A best approximation is one of the two bracket endpoints, and both of those are reduced.
-/
public theorem Arguments.reduced_of_best (args : Arguments) {ef : Candidate args}
    (hef : ef.best) : ef.reduced := by
  let st := args.postLoopState
  rcases st.eq_rs_or_eq_tu_of_best hef with rfl | rfl
  · exact st.reduced_rs
  · exact st.reduced_tu
