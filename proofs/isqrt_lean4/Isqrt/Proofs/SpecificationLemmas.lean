/-
Bridging lemmas for the proof-carrying specification helpers of
`Isqrt.Definitions.Specification`. Reducing an `isqrt` `do`-block yields a plain
equality — `isqrt n = .ok a` or `isqrt n = .error e`. These two lemmas repackage
such an equality into the dependent existential the specification is phrased with
(`∃ h : succeeds x, …(returnValue x h)` and its `fails`/`exceptionRaised` twin),
discharging the success/failure proof and the `returnValue`/`exceptionRaised` extraction
by reduction. They are the only glue the correctness proofs need to talk to the
proof-carrying spec.
-/

import Isqrt.Definitions.Specification

/-- From `x = .ok a` and `p a`: the computation `x` succeeded, and its returned
value satisfies `p`. Repackages the `.ok` equality a reduced `do`-block produces
into the dependent existential `isCorrectIsqrt` uses. -/
theorem returnValue_satisfies {ε α : Type _} {x : Except ε α} {a : α} (hx : x = .ok a)
    (p : α → Prop) (hp : p a) : ∃ h : Isqrt.succeeds x, p (Isqrt.returnValue x h) := by
  subst hx; exact ⟨True.intro, hp⟩

/-- From `x = .error e` and `q e`: the computation `x` failed, and its raised
exception satisfies `q`. The `fails`/`exceptionRaised` twin of `returnValue_satisfies`. -/
theorem exceptionRaised_satisfies {ε α : Type _} {x : Except ε α} {e : ε} (hx : x = .error e)
    (q : ε → Prop) (hq : q e) : ∃ h : Isqrt.fails x, q (Isqrt.exceptionRaised x h) := by
  subst hx; exact ⟨True.intro, hq⟩
