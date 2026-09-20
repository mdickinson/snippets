module

public import LimitDenominator.Definitions.LimitDenominatorSimplified
public import LimitDenominator.Proofs.Experiment
import LimitDenominator.Proofs.PythonTranslation
import LimitDenominator.Proofs.WhileLoop

/-!
Correctness of `limitDenominatorSimplified`.

This file is the mechanics: it names the two halves of the `do` block — `loopBody`
and `afterLoop` — folds the translation onto them, identifies the loop with
`runLoop`, and reads the result off. All of the mathematics has already happened,
in `Experiment`.

The six-tuple state appears only here. `LoopState` carries the same six numbers with
their invariants and the orientation attached, and `loopTuple` is the projection
onto the tuple.
-/

/-- The mutable state of the loop: `(a, b, p, q, r, s)`. -/
abbrev LoopTuple := Int × Int × Int × Int × Int × Int

/--
The loop body, named. This is definitionally what `limitDenominatorSimplified`'s `do` block
desugars to, so `limitDenominatorSimplified_fold` folds the loop onto it by `rfl`.
-/
def loopBody (l : Int) (_u : Unit) (state : LoopTuple) : PyExcept (ForInStep LoopTuple) :=
  let ⟨a, b, p, q, r, s⟩ := state
  do
    let cond ← pure (0 < b : Bool) <&&> (do return q + (← pyFloordiv a b) * s ≤ l)
    if cond = true then
      pure (ForInStep.yield
        (b, ← pyMod a b, r, s, p + (← pyFloordiv a b) * r, q + (← pyFloordiv a b) * s))
    else
      pure (ForInStep.done (a, b, p, q, r, s))

/-- The tail of the `do` block, named likewise: the extended candidate and the final choice. -/
def afterLoop (n l : Int) (state : LoopTuple) : PyExcept (Int × Int) :=
  let ⟨_a, b, p, q, r, s⟩ := state
  do
    let k ← pyFloordiv (l - q) s
    pure (if 2 * b * (q + k * s) ≤ n then (r, s) else (p + k * r, q + k * s))

/-- `limitDenominatorSimplified` on a valid target, as a loop followed by its tail. -/
theorem limitDenominatorSimplified_fold {m n l : Int} (hn : 0 < n) (hl : 0 < l) :
    limitDenominatorSimplified m n l =
      forIn Lean.Loop.mk (n, m % n, 1, 0, m / n, 1) (loopBody l) >>= afterLoop n l := by
  rw [limitDenominatorSimplified, ite_eq_right (by omega), ite_eq_right (by omega),
    pyMod_ok_bind hn, pyFloordiv_ok_bind hn]
  rfl

/-! ## Reducing the loop body -/

/--
With `b` zero, Python's `and` short-circuits: the right operand — which would divide by zero — is
never evaluated, and the loop exits.
-/
theorem loopBody_of_zero (l a p q r s : Int) :
    loopBody l () (a, 0, p, q, r, s) = pure (ForInStep.done (a, 0, p, q, r, s)) := by
  rw [loopBody, show decide ((0 : Int) < 0) = false from by decide, andM_pure_false, pure_bind,
    ite_eq_right (by decide)]

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

/-- The six numbers a loop state carries, as the tuple the `do` block threads. -/
def loopTuple {args : Arguments} (st : LoopState args) : LoopTuple :=
  (st.a, st.b, st.p, st.q, st.r, st.s)

/-- Where the loop condition holds, one iteration of the body is one `nextLoopState`. -/
theorem loopBody_of_loopCondition {args : Arguments} {st : LoopState args}
    (hst : st.loopCondition) :
    loopBody args.limit () (loopTuple st) =
      pure (ForInStep.yield (loopTuple (st.nextLoopState hst))) := by
  show loopBody args.limit () (st.a, st.b, st.p, st.q, st.r, st.s) = _
  rw [loopBody_of_pos hst.1, ite_eq_left hst.2]
  rfl

/-- Where it fails, the body is done and leaves the state as it stands. -/
theorem loopBody_of_not_loopCondition {args : Arguments} {st : LoopState args}
    (hst : ¬ st.loopCondition) :
    loopBody args.limit () (loopTuple st) = pure (ForInStep.done (loopTuple st)) := by
  show loopBody args.limit () (st.a, st.b, st.p, st.q, st.r, st.s) =
    pure (ForInStep.done (st.a, st.b, st.p, st.q, st.r, st.s))
  rcases (by have := st.b_nonneg; omega : st.b = 0 ∨ 0 < st.b) with hb | hb
  · rw [hb]; exact loopBody_of_zero args.limit st.a st.p st.q st.r st.s
  · rw [loopBody_of_pos hb, ite_eq_right (fun hle => hst ⟨hb, hle⟩)]

/-- The `do` block's loop, run to exhaustion, is `runLoop`. -/
theorem forIn_eq_runLoop {args : Arguments} (st : LoopState args) :
    forIn Lean.Loop.mk (loopTuple st) (loopBody args.limit) =
      pure (loopTuple st.runLoop) := by
  fun_induction LoopState.runLoop st with
  | case1 st hst ih => rw [forIn_loop_peel _ (loopBody_of_loopCondition hst), ih]
  | case2 st hst => exact forIn_loop_done _ (loopBody_of_not_loopCondition hst)

/-- The tail of the `do` block is the post-loop state's return value. -/
theorem afterLoop_eq {args : Arguments} (st : PostLoopState args) :
    afterLoop args.n args.limit (loopTuple st.toLoopState) =
      pure (st.rv.num, st.rv.den) := by
  show afterLoop args.n args.limit (st.a, st.b, st.p, st.q, st.r, st.s) = _
  rw [afterLoop, pyFloordiv_ok_bind st.s_pos]
  show pure (if 2 * st.b * st.u ≤ args.n then (st.r, st.s) else (st.t, st.u)) = _
  rw [PostLoopState.rv]
  split <;> rfl

/-- The listing computes the algorithm, end to end. -/
theorem limitDenominatorSimplified_eq (args : Arguments) :
    limitDenominatorSimplified args.m args.n args.limit =
      pure (args.limitDenominator.num, args.limitDenominator.den) := by
  rw [limitDenominatorSimplified_fold args.n_pos (by have := args.one_le_limit; omega)]
  show forIn Lean.Loop.mk (loopTuple (LoopState.initialLoopState args)) _ >>= _ = _
  rw [forIn_eq_runLoop, pure_bind]
  exact afterLoop_eq args.postLoopState

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
    rw [limitDenominatorSimplified, ite_eq_left (show l < 1 by omega)]
    rfl
  · -- Otherwise the listing computes the algorithm, whose answer is best.
    intro m n l hn hl
    let args : Arguments := ⟨m, n, l, hn, by omega⟩
    exact ⟨args.limitDenominator.num, args.limitDenominator.den,
      limitDenominatorSimplified_eq args,
      (best_iff_isBestApproximation _).mp args.limitDenominator_best⟩

/--
A target denominator that is not positive raises a `ValueError`. The denominator limit is
checked first, so this needs the limit to have passed its own check.
-/
public theorem limitDenominatorSimplified_raises_of_denominator_nonpos {m n l : Int}
    (hn : n ≤ 0) (hl : 0 < l) :
    raises (limitDenominatorSimplified m n l) (.valueError "denominator should be positive") := by
  rw [limitDenominatorSimplified, ite_eq_right (by omega), ite_eq_left hn]
  rfl

/--
In the ambiguous case the two best approximations are `⌊m/n⌋` and `⌊m/n⌋ + 1`, and
the listing returns the lower of them. This is the tie-break CPython makes, and the
one the specification deliberately leaves open.
-/
public theorem limitDenominatorSimplified_returns_floor_of_ambiguous {m n l : Int}
    (hn : 0 < n) (hamb : isAmbiguous m n l) :
    returns (limitDenominatorSimplified m n l) (m / n, 1) := by
  let args : Arguments := ⟨m, n, l, hn, by have := hamb.1; omega⟩
  have heq := limitDenominatorSimplified_eq args
  have hamb' := (ambiguous_iff_isAmbiguous args).mpr hamb
  rw [args.limitDenominator_ambiguous_case hamb'] at heq
  exact heq

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
