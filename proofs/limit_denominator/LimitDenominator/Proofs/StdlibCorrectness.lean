module

public import LimitDenominator.Definitions.LimitDenominatorStdlib
public import LimitDenominator.Proofs.Experiment
import LimitDenominator.Proofs.PythonTranslation
import LimitDenominator.Proofs.WhileLoop

/-!
Correctness of `limitDenominatorStdlib`.

Like `SimplifiedCorrectness`, this file is the mechanics: it names the two halves of the
`do` block, folds the translation onto them, identifies the loop with `runLoop`, and
reads the result off.

The shipped listing's state is the proof layer's, permuted: its `(p0, q0, p1, q1, n, d)`
is `(p, q, r, s, a, b)`, and `stdlibTuple` projects in that order. Two things come from
the listing's shape rather than the algorithm's:

* **The first iteration is peeled off.** It cannot break, its `q2` being `1`, and it
  computes exactly the initial loop state, which the state before it is not: `s` there
  is `q1 = 0`.
* **`0 < b` is derived rather than tested.** The shipped loop condition omits that test,
  so the divisor's positivity comes from `LoopState.b_pos`, and that is where the
  target's being in lowest terms earns its place among the hypotheses.

The fast path is none of this: it discharges against the specification directly.
-/

/-- The mutable state of the loop: `(p, q, r, s, a, b)`, the shipped
`(p0, q0, p1, q1, n, d)`. -/
abbrev StdlibLoopTuple := Int × Int × Int × Int × Int × Int

/--
The loop body, named. This is definitionally what `limitDenominatorStdlib`'s `do` block
desugars to, so `limitDenominatorStdlib_fold` folds the loop onto it by `rfl`. The
`break` is the `ForInStep.done`, carrying the state out unchanged.
-/
def stdlibLoopBody (l : Int) (_u : Unit) (state : StdlibLoopTuple) :
    PyExcept (ForInStep StdlibLoopTuple) :=
  let ⟨p, q, r, s, a, b⟩ := state
  do
    let k ← pyFloordiv a b
    let q2 := q + k * s
    if q2 > l then
      pure (ForInStep.done state)
    else
      pure (ForInStep.yield (r, s, p + k * r, q2, b, a - k * b))

/--
The tail of the `do` block, named likewise: the extended candidate and the final choice.

Here `n` is the *target's* denominator, the shipped code's `self._denominator`. The
Python's own `n` is the running numerator, which is this state's `_a`, and is unused
past the loop.
-/
def stdlibAfterLoop (n l : Int) (state : StdlibLoopTuple) : PyExcept (Int × Int) :=
  let ⟨p, q, r, s, _a, b⟩ := state
  do
    let k ← pyFloordiv (l - q) s
    if 2 * b * (q + k * s) ≤ n then pure (r, s) else pure (p + k * r, q + k * s)

/-- `limitDenominatorStdlib` past both guards, as a loop followed by its tail. -/
theorem limitDenominatorStdlib_fold {m n l : Int} (hl : 0 < l) (hn : l < n) :
    limitDenominatorStdlib m n l =
      forIn Lean.Loop.mk (0, 1, 1, 0, m, n) (stdlibLoopBody l) >>= stdlibAfterLoop n l := by
  rw [limitDenominatorStdlib, ite_eq_right (by omega), ite_eq_right (by omega)]
  rfl

/-! ## Peeling the first iteration -/

/--
The first iteration in full. Its break test weighs `q + ks` — here `1 + (m/n)·0`, or
just `1` — against a positive limit, so it never breaks; and it divides by the target's
denominator, so it cannot raise. The state it lands on is the initial loop state.
-/
theorem stdlibLoopBody_initial {m n l : Int} (hn : 0 < n) (hl : 0 < l) :
    stdlibLoopBody l () (0, 1, 1, 0, m, n)
      = pure (ForInStep.yield (1, 0, m / n, 1, n, m % n)) := by
  have h : m - m / n * n = m % n := by have := Int.mul_ediv_add_emod m n; grind
  rw [stdlibLoopBody, pyFloordiv_ok_bind hn, ite_eq_right (by omega), h]
  simp

/-! ## Driving the loop -/

/-- The six numbers a loop state carries, in the order the shipped listing threads
them. -/
def stdlibTuple {args : Arguments} (st : LoopState args) : StdlibLoopTuple :=
  (st.p, st.q, st.r, st.s, st.a, st.b)

/-- Where the loop condition holds, one iteration of the body is one `nextLoopState`. -/
theorem stdlibLoopBody_of_loopCondition {args : Arguments} {st : LoopState args}
    (hst : st.loopCondition) :
    stdlibLoopBody args.limit () (stdlibTuple st) =
      pure (ForInStep.yield (stdlibTuple (st.nextLoopState hst))) := by
  have hmod : st.a - st.a / st.b * st.b = st.a % st.b := by
    have := Int.mul_ediv_add_emod st.a st.b; grind
  show stdlibLoopBody args.limit () (st.p, st.q, st.r, st.s, st.a, st.b) = _
  rw [stdlibLoopBody, pyFloordiv_ok_bind hst.1]
  -- Beta-reduce the `q2` binding, which `rw` cannot see past.
  simp only []
  rw [ite_eq_right (by have := hst.2; omega), hmod]
  rfl

/-- Where it fails, the body breaks and carries the state out as it stands. -/
theorem stdlibLoopBody_of_not_loopCondition {args : Arguments} {st : LoopState args}
    (hb : 0 < st.b) (hst : ¬ st.loopCondition) :
    stdlibLoopBody args.limit () (stdlibTuple st) =
      pure (ForInStep.done (stdlibTuple st)) := by
  have hgt : args.limit < st.q + st.a / st.b * st.s := by
    by_cases hle : st.q + st.a / st.b * st.s ≤ args.limit
    · exact absurd ⟨hb, hle⟩ hst
    · omega
  show stdlibLoopBody args.limit () (st.p, st.q, st.r, st.s, st.a, st.b) = _
  rw [stdlibLoopBody, pyFloordiv_ok_bind hb]
  simp only []
  rw [ite_eq_left (by omega)]
  rfl

/--
The `do` block's loop, run to exhaustion, is `runLoop`. The two conditions coincide only
where `b` is positive, which is what brings the target's hypotheses in here.
-/
theorem forIn_eq_runLoop_stdlib {args : Arguments} (hgcd : Int.gcd args.m args.n = 1)
    (hlim : args.limit < args.n) (st : LoopState args) :
    forIn Lean.Loop.mk (stdlibTuple st) (stdlibLoopBody args.limit) =
      pure (stdlibTuple st.runLoop) := by
  fun_induction LoopState.runLoop st with
  | case1 st hst ih => rw [forIn_loop_peel _ (stdlibLoopBody_of_loopCondition hst), ih]
  | case2 st hst =>
    exact forIn_loop_done _
      (stdlibLoopBody_of_not_loopCondition (st.b_pos hgcd hlim) hst)

/-- The tail of the `do` block is the post-loop state's return value. -/
theorem stdlibAfterLoop_eq {args : Arguments} (st : PostLoopState args) :
    stdlibAfterLoop args.n args.limit (stdlibTuple st.toLoopState) =
      pure (st.rv.num, st.rv.den) := by
  show stdlibAfterLoop args.n args.limit (st.p, st.q, st.r, st.s, st.a, st.b) = _
  rw [stdlibAfterLoop, pyFloordiv_ok_bind st.s_pos]
  show (if 2 * st.b * st.u ≤ args.n then pure (st.r, st.s) else pure (st.t, st.u)) = _
  rw [PostLoopState.rv]
  split <;> rfl

/-- Past the fast path, the listing computes the algorithm, end to end. -/
theorem limitDenominatorStdlib_eq (args : Arguments) (hgcd : Int.gcd args.m args.n = 1)
    (hlim : args.limit < args.n) :
    limitDenominatorStdlib args.m args.n args.limit =
      pure (args.limitDenominator.num, args.limitDenominator.den) := by
  have hl : 0 < args.limit := by have := args.one_le_limit; omega
  rw [limitDenominatorStdlib_fold hl hlim,
    forIn_loop_peel _ (stdlibLoopBody_initial args.n_pos hl)]
  show forIn Lean.Loop.mk (stdlibTuple (LoopState.initialLoopState args)) _ >>= _ = _
  rw [forIn_eq_runLoop_stdlib hgcd hlim, pure_bind]
  exact stdlibAfterLoop_eq args.postLoopState

/--
Correctness of `limitDenominatorStdlib`: for a denominator limit that is not positive it
raises the same `ValueError` as CPython, and for a target in lowest terms with positive
denominator — which is every target a `Fraction` can hold — it returns the best
approximation.
-/
public theorem isCorrectLimitDenominator_stdlib :
    isCorrectLimitDenominator (fun m n => 0 < n ∧ Int.gcd m n = 1) limitDenominatorStdlib := by
  refine ⟨?_, ?_⟩
  · -- A nonpositive limit: the first guard raises, short-circuiting the `do` block.
    intro m n l hl
    rw [limitDenominatorStdlib, ite_eq_left (show l < 1 by omega)]
    rfl
  · intro m n l ⟨hn, hgcd⟩ hl
    rcases (by omega : n ≤ l ∨ l < n) with hfast | hslow
    · -- The fast path returns the target itself.
      refine ⟨m, n, ?_, isBestApproximation_self hn hfast hgcd⟩
      rw [limitDenominatorStdlib, ite_eq_right (by omega), ite_eq_left hfast]
      rfl
    -- Otherwise the listing computes the algorithm, whose answer is best.
    let args : Arguments := ⟨m, n, l, hn, by omega⟩
    exact ⟨args.limitDenominator.num, args.limitDenominator.den,
      limitDenominatorStdlib_eq args hgcd hslow,
      (best_iff_isBestApproximation _).mp args.limitDenominator_best⟩

/--
In the ambiguous case the two best approximations are `⌊m/n⌋` and `⌊m/n⌋ + 1`, and the
listing returns the lower of them. A target in lowest terms is ambiguous only at `n = 2`
with `l = 1`, so the fast path is never the ambiguous one and this lives wholly on the
loop path.
-/
public theorem limitDenominatorStdlib_returns_floor_of_ambiguous {m n l : Int}
    (hn : 0 < n) (hgcd : Int.gcd m n = 1) (hamb : isAmbiguous m n l) :
    returns (limitDenominatorStdlib m n l) (m / n, 1) := by
  obtain ⟨hl, w, hw⟩ := hamb
  have hslow : l < n := by
    rcases (by omega : n = 1 ∨ 1 < n) with rfl | h1 <;> omega
  let args : Arguments := ⟨m, n, l, hn, by omega⟩
  have heq := limitDenominatorStdlib_eq args hgcd hslow
  have hamb' := (ambiguous_iff_isAmbiguous args).mpr ⟨hl, w, hw⟩
  rw [args.limitDenominator_ambiguous_case hamb'] at heq
  exact heq
