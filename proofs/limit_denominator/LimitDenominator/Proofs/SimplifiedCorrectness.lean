module

public import LimitDenominator.Definitions.LimitDenominatorSimplified
public import LimitDenominator.Definitions.Specification
public import LimitDenominator.Proofs.BestApproximation
import LimitDenominator.Proofs.PythonTranslation
import LimitDenominator.Proofs.WhileLoop

/-!
Correctness of `limitDenominatorSimplified`.

This file is the mechanics: it names the two halves of the `do` block — `loopBody` and
`afterLoop` — folds the translation onto them, drives the loop with `forIn_loop_invariant`, and
reads the result off. All of the mathematics has already happened, in `BestApproximation`.

The six-tuple state appears only here. `LoopInvariant` and `Bracketing` take plain `Int`
arguments and never project out of a tuple.
-/

/-- The mutable state of the loop: `(a, b, p, q, r, s)`. -/
abbrev LoopState := Int × Int × Int × Int × Int × Int

/--
The loop body, named. This is definitionally what `limitDenominatorSimplified`'s `do` block
desugars to, so `limitDenominatorSimplified_fold` folds the loop onto it by `rfl`.
-/
def loopBody (l : Int) (_u : Unit) (state : LoopState) : PyExcept (ForInStep LoopState) :=
  let ⟨a, b, p, q, r, s⟩ := state
  do
    let cond ← pure (0 < b : Bool) <&&> (do return q + (← pyFloordiv a b) * s ≤ l)
    if cond = true then
      pure (ForInStep.yield
        (b, ← pyMod a b, r, s, p + (← pyFloordiv a b) * r, q + (← pyFloordiv a b) * s))
    else
      pure (ForInStep.done (a, b, p, q, r, s))

/-- The tail of the `do` block, named likewise: the extended candidate and the final choice. -/
def afterLoop (n l : Int) (state : LoopState) : PyExcept (Int × Int) :=
  let ⟨_a, b, p, q, r, s⟩ := state
  do
    -- Two bindings for one quotient, because the Python writes `(l - q) // s` twice:
    -- collapsing them breaks the `rfl` in `limitDenominatorSimplified_fold`.
    let k1 ← pyFloordiv (l - q) s
    let k2 ← pyFloordiv (l - q) s
    pure (if 2 * b * (q + k2 * s) ≤ n then (r, s) else (p + k1 * r, q + k2 * s))

/-- `limitDenominatorSimplified` on a valid target, as a loop followed by its tail. -/
theorem limitDenominatorSimplified_fold {m n l : Int} (hn : 0 < n) (hl : 0 < l) :
    limitDenominatorSimplified m n l =
      forIn Lean.Loop.mk (n, m % n, 1, 0, m / n, 1) (loopBody l) >>= afterLoop n l := by
  rw [limitDenominatorSimplified, if_neg (by omega), if_neg (by omega), pyMod_ok_bind hn,
    pyFloordiv_ok_bind hn]
  rfl

/-! ## Reducing the loop body -/

/--
With `b` zero, Python's `and` short-circuits: the right operand — which would divide by zero — is
never evaluated, and the loop exits.
-/
theorem loopBody_of_zero (l a p q r s : Int) :
    loopBody l () (a, 0, p, q, r, s) = pure (ForInStep.done (a, 0, p, q, r, s)) := by
  rw [loopBody, show decide ((0 : Int) < 0) = false from by decide, andM_pure_false, pure_bind,
    if_neg (by decide)]

/-- With `b` positive, the body divides safely and the exit test is the Python condition. -/
theorem loopBody_of_pos {l a b p q r s : Int} (hb : 0 < b) :
    loopBody l () (a, b, p, q, r, s) =
      if q + a / b * s ≤ l then
        pure (ForInStep.yield (b, a % b, r, s, p + a / b * r, q + a / b * s))
      else
        pure (ForInStep.done (a, b, p, q, r, s)) := by
  rw [loopBody, decide_eq_true hb, andM_pure_true, pyFloordiv_ok_bind hb, pure_bind]
  simp only [decide_eq_true_eq]
  split
  · rw [pyMod_ok_bind hb, pyFloordiv_ok_bind hb, pyFloordiv_ok_bind hb]
  · rfl

/-! ## Driving the loop -/

/-- The loop invariant, as a predicate on the loop's state. -/
def loopInvariant (m n l : Int) (state : LoopState) : Prop :=
  let ⟨a, b, p, q, r, s⟩ := state
  LoopInvariant m n l a b p q r s

/-- The loop invariant together with the negation of the loop condition. -/
def loopPost (m n l : Int) (state : LoopState) : Prop :=
  let ⟨a, b, p, q, r, s⟩ := state
  LoopInvariant m n l a b p q r s ∧ (b = 0 ∨ (0 < b ∧ l < q + a / b * s))

/--
Under the invariant the body never raises: it either yields a state that still satisfies the
invariant with a strictly smaller `b`, or finishes with the loop condition false.
-/
theorem loopBody_step (m n l : Int) (state : LoopState) (hinv : loopInvariant m n l state) :
    (∃ state', loopBody l () state = pure (ForInStep.yield state')
        ∧ loopInvariant m n l state' ∧ state'.2.1.toNat < state.2.1.toNat)
    ∨ (∃ state', loopBody l () state = pure (ForInStep.done state') ∧ loopPost m n l state') := by
  obtain ⟨a, b, p, q, r, s⟩ := state
  have h : LoopInvariant m n l a b p q r s := hinv
  rcases (by have := h.b_nonneg; omega : b = 0 ∨ 0 < b) with rfl | hb
  · exact .inr ⟨_, loopBody_of_zero l a p q r s, h, .inl rfl⟩
  rw [loopBody_of_pos hb]
  split
  · exact .inl ⟨_, rfl, h.step hb (by assumption),
      (Int.toNat_lt_toNat hb).mpr (Int.emod_lt_of_pos a hb)⟩
  · exact .inr ⟨_, rfl, h, .inr ⟨hb, by omega⟩⟩

/--
Correctness of `limitDenominatorSimplified`: for a denominator limit that is not positive it
raises the same `ValueError` as CPython, and for a target with positive denominator it returns
the best approximation.
-/
public theorem isCorrectLimitDenominator_simplified :
    isCorrectLimitDenominator (fun _ n => 0 < n) limitDenominatorSimplified := by
  refine ⟨?_, ?_⟩
  · -- A nonpositive limit: the first guard raises, short-circuiting the `do` block.
    intro m n l hl
    rw [limitDenominatorSimplified, if_pos (show l < 1 by omega)]
    rfl
  · -- Otherwise the loop runs, never raises, and returns one of the two candidates.
    intro m n l hn hl
    rw [limitDenominatorSimplified_fold hn hl]
    obtain ⟨y, hy_eq, hy_post⟩ := forIn_loop_invariant
      (fun state => state.2.1.toNat) (loopBody l) (loopInvariant m n l) (loopPost m n l)
      (loopBody_step m n l) (n, m % n, 1, 0, m / n, 1) (LoopInvariant.initial hn hl)
    rw [hy_eq]
    obtain ⟨a, b, p, q, r, s⟩ := y
    obtain ⟨hinv, hexit⟩ :
        LoopInvariant m n l a b p q r s ∧ (b = 0 ∨ (0 < b ∧ l < q + a / b * s)) := hy_post
    rw [afterLoop, pyFloordiv_ok_bind hinv.s_pos, pyFloordiv_ok_bind hinv.s_pos]
    have hbracket := hinv.bracketing hexit rfl rfl rfl rfl
    split <;> rename_i hchoice
    · exact ⟨r, s, rfl, hbracket.isBestApproximation_loop_of_test hchoice⟩
    · exact ⟨_, _, rfl, hbracket.isBestApproximation_extended_of_test hchoice⟩

/--
A target denominator that is not positive raises a `ValueError`. The denominator limit is
checked first, so this needs the limit to have passed its own check.
-/
public theorem limitDenominatorSimplified_raises_of_denominator_nonpos {m n l : Int}
    (hn : n ≤ 0) (hl : 0 < l) :
    raises (limitDenominatorSimplified m n l) (.valueError "denominator should be positive") := by
  rw [limitDenominatorSimplified, if_neg (by omega), if_pos hn]
  rfl

/--
Every input is accounted for: the function raises one of its two `ValueError`s or returns the
best approximation, and nothing else can happen. In particular no input receives a wrong answer.

Which of the three cases applies is settled by `isCorrectLimitDenominator_simplified` and
`limitDenominatorSimplified_raises_of_denominator_nonpos`; this theorem adds only that the cases
are exhaustive.
-/
public theorem limitDenominatorSimplified_total (m n l : Int) :
    raises (limitDenominatorSimplified m n l) (.valueError "max_denominator should be at least 1")
    ∨ raises (limitDenominatorSimplified m n l) (.valueError "denominator should be positive")
    ∨ ∃ r s, returns (limitDenominatorSimplified m n l) (r, s)
        ∧ isBestApproximation m n l r s := by
  obtain ⟨hraises, hreturns⟩ := isCorrectLimitDenominator_simplified
  rcases (by omega : l ≤ 0 ∨ 0 < l) with hl | hl
  · exact .inl (hraises hl)
  rcases (by omega : n ≤ 0 ∨ 0 < n) with hn | hn
  · exact .inr (.inl (limitDenominatorSimplified_raises_of_denominator_nonpos hn hl))
  · exact .inr (.inr (hreturns hn hl))
