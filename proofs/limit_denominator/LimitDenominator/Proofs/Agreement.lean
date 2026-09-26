module

public import LimitDenominator.Definitions.LimitDenominatorSimplified
public import LimitDenominator.Definitions.LimitDenominatorStdlib
import LimitDenominator.Proofs.SimplifiedCorrectness
import LimitDenominator.Proofs.StdlibCorrectness

/-!
The two listings agree on every target the shipped one accepts.
-/

/--
On a target in lowest terms with positive denominator, the shipped listing and the
simplified one are the same function: the same `ValueError` for a limit below one, and
the same pair otherwise.

The proof does not look inside either listing. Each is correct, the specification
determines the answer outside the ambiguous case, and inside it the two listings make
the same tie-break; that is enough.
-/
public theorem limitDenominatorStdlib_eq_limitDenominatorSimplified {m n l : Int}
    (hn : 0 < n) (hgcd : Int.gcd m n = 1) :
    limitDenominatorStdlib m n l = limitDenominatorSimplified m n l := by
  obtain ⟨stdlib_raises, stdlib_returns⟩ := isCorrectLimitDenominator_stdlib
  obtain ⟨simplified_raises, simplified_returns⟩ := isCorrectLimitDenominator_simplified
  rcases (by omega : l ≤ 0 ∨ 0 < l) with hl | hl
  · exact Eq.trans (stdlib_raises hl) (simplified_raises hl).symm
  by_cases hamb : isAmbiguous m n l
  · exact Eq.trans (limitDenominatorStdlib_returns_floor_of_ambiguous hn hgcd hamb)
      (limitDenominatorSimplified_returns_floor_of_ambiguous hn hamb).symm
  · obtain ⟨r₁, s₁, h₁, hbest₁⟩ := stdlib_returns ⟨hn, hgcd⟩ hl
    obtain ⟨r₂, s₂, h₂, hbest₂⟩ := simplified_returns hn hl
    obtain ⟨rfl, rfl⟩ :=
      isBestApproximation_unique_of_not_ambiguous hn hamb hbest₁ hbest₂
    exact Eq.trans h₁ h₂.symm
