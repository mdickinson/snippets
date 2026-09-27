module

public import LimitDenominator.Proofs.Arguments
public import LimitDenominator.Proofs.Candidate
import LimitDenominator.Proofs.IntLemmas

/-!
The algorithm, as the proof layer computes it: the loop state and its invariants, one
iteration and the whole loop, the state on exit with its pure and mixed candidates and
the mixed candidate's residual `c`, and the return value.
-/

/-! # In the loop -/

/-
The loop is the Euclidean algorithm on `m` and `n`, tracking the continued-fraction
convergents of `m/n` as it goes. `a > b ≥ 0` are the two most recent remainders. `r/s`
is the most recent convergent and `p/q` the one before it, starting from `⌊m/n⌋/1` and
`1/0`, so `q = 0` only in the initial state. Consecutive convergents lie on opposite
sides of `m/n`; `v ∈ {1, -1}` records which way round, with `r/s ≤ m/n < p/q` when
`v = 1` and `p/q < m/n ≤ r/s` when `v = -1`. The orientation reverses on every
iteration.

The invariants tie the remainders to the convergents. `det` is the
consecutive-convergent identity `p * s - r * q = ±1`, with `v` as the sign.
`a_eq_pq_cross` and `b_eq_rs_cross` say that `a` and `b` are the cross-multiplied
distances `|p * n - m * q|` and `|m * s - r * n|` from `m/n` to the two convergents,
again with `v` supplying the sign. `s_le_limit` is what the loop condition checked
before stepping to this state.
-/

/--
The loop state: the two latest Euclidean remainders, the two latest convergents, and
the orientation `v`.
-/
public structure LoopState (args : Arguments) where
  /-- The larger of the two most recent Euclidean remainders. -/
  a : Int
  /-- The smaller of the two most recent Euclidean remainders. -/
  b : Int
  /-- Numerator of the previous convergent `p/q`. -/
  p : Int
  /-- Denominator of the previous convergent `p/q`. -/
  q : Int
  /-- Numerator of the most recent convergent `r/s`. -/
  r : Int
  /-- Denominator of the most recent convergent `r/s`. -/
  s : Int
  /-- The orientation. -/
  v : Int
  b_nonneg : 0 ≤ b
  b_lt_a : b < a
  q_nonneg : 0 ≤ q
  s_pos : 0 < s
  s_le_limit : s ≤ args.limit
  det : (p * s - r * q) * v = 1
  a_eq_pq_cross : (p * args.n - args.m * q) * v = a
  b_eq_rs_cross : (args.m * s - r * args.n) * v = b
  v_eq_one_of_q_eq_zero : q = 0 → v = 1

namespace LoopState

variable {args : Arguments} (st : LoopState args)

/-- The state before the first iteration. -/
@[expose] public def initialLoopState (args : Arguments) : LoopState args where
  a := args.n
  b := args.m % args.n
  p := 1
  q := 0
  r := args.m / args.n
  s := 1
  v := 1
  det := by grind only
  b_nonneg := Int.emod_nonneg args.m (Int.ne_of_gt args.n_pos)
  b_lt_a := Int.emod_lt_of_pos args.m args.n_pos
  q_nonneg := by decide
  s_pos := by decide
  s_le_limit := args.one_le_limit
  a_eq_pq_cross := by grind only
  b_eq_rs_cross := by grind only [Int.mul_ediv_add_emod args.m args.n]
  v_eq_one_of_q_eq_zero := by decide

/-- Condition guarding iteration of the while loop. -/
@[expose] public def loopCondition := 0 < st.b ∧ st.q + st.a / st.b * st.s ≤ args.limit

/-- The state transition resulting from execution of the loop body. -/
@[expose] public def nextLoopState (hst : st.loopCondition) : LoopState args where
  a := st.b
  b := st.a % st.b
  p := st.r
  q := st.s
  r := st.p + st.a / st.b * st.r
  s := st.q + st.a / st.b * st.s
  v := -st.v
  det := by grind only [st.det]
  b_nonneg := Int.emod_nonneg st.a (Int.ne_of_gt hst.1)
  b_lt_a := Int.emod_lt_of_pos st.a hst.1
  q_nonneg := Int.le_of_lt st.s_pos
  s_pos := by
    have a_ediv_b_pos : 0 < st.a / st.b :=
      (Int.le_ediv_iff_mul_le hst.1).mpr (by grind only [st.b_lt_a])
    grind only [st.q_nonneg, Int.mul_pos a_ediv_b_pos st.s_pos]
  s_le_limit := hst.2
  a_eq_pq_cross := by grind only [st.b_eq_rs_cross]
  b_eq_rs_cross := by
    grind only [st.a_eq_pq_cross, st.b_eq_rs_cross, Int.mul_ediv_add_emod st.a st.b]
  v_eq_one_of_q_eq_zero := by grind only [st.s_pos]

/-- The termination measure for the loop: `max(a, 0)`, as a `Nat`. -/
public def loopMeasure : Nat := st.a.toNat

/-- The measure strictly decreases with each iteration of the loop. -/
theorem loopMeasure_decreasing (hst : st.loopCondition) :
    (st.nextLoopState hst).loopMeasure < st.loopMeasure :=
  (Int.toNat_lt_toNat (Int.lt_of_le_of_lt st.b_nonneg st.b_lt_a)).mpr st.b_lt_a

/-! ## Execution of the loop -/

/-- The loop condition is decidable. -/
public instance : Decidable st.loopCondition := by unfold loopCondition; infer_instance

/-- Starting from a given state, run the loop to completion. -/
@[expose] public def runLoop (st : LoopState args) : LoopState args :=
  if h : st.loopCondition then runLoop (st.nextLoopState h) else st
termination_by st.loopMeasure
decreasing_by exact st.loopMeasure_decreasing h

/-- On exit of the loop, the loop condition is false. -/
public theorem runLoop_loopCondition_false : ¬ st.runLoop.loopCondition := by
  fun_induction runLoop st <;> trivial

end LoopState

/-! # On exit from the loop -/

/-- State on exiting the loop: a loop state whose loop condition has gone false. -/
public structure PostLoopState (args : Arguments) extends LoopState args where
  exited : ¬ toLoopState.loopCondition

namespace PostLoopState

/- We fix a post-loop state `st` throughout this section. -/
variable {args : Arguments} (st : PostLoopState args)

/-! ## The pure candidate -/

/-- The pure candidate `r/s`, the loop's own, packaged as a `Candidate`. -/
public abbrev rs : Candidate args := ⟨st.r, st.s, st.s_pos, st.s_le_limit⟩

/-! ## The mixed candidate -/

/--
The number of copies of `r/s` that can be "added" to `p/q` without the denominator
exceeding the limit.
-/
@[expose] public def k : Int := (args.limit - st.q) / st.s

/-- Numerator of the mixed candidate: `t/u` is `p/q` plus `k` copies of `r/s`. -/
@[expose] public def t : Int := st.p + st.k * st.r
/-- Denominator of the mixed candidate. -/
@[expose] public def u : Int := st.q + st.k * st.s

/-- From the definition of `k` we have `ks ≤ limit - q`, giving `u ≤ limit`. -/
public theorem u_le_limit : st.u ≤ args.limit := by
  grind only [k, u, Int.ediv_mul_le (args.limit - st.q) (Int.ne_of_gt st.s_pos)]

/--
From the definition of `k` we have `limit - q < (k + 1)s`, giving `limit < s + u`.
-/
public theorem limit_lt_s_add_u : args.limit < st.s + st.u := by
  grind only [k, u, Int.lt_ediv_mul (args.limit - st.q) st.s_pos]

/-- Since `s ≤ limit < s + u`, it follows that `0 < u`. -/
public theorem u_pos : 0 < st.u := by grind only [st.s_le_limit, st.limit_lt_s_add_u]

/-- The mixed candidate `t/u`, packaged as a `Candidate`. -/
public abbrev tu : Candidate args := ⟨st.t, st.u, st.u_pos, st.u_le_limit⟩

/-- The loop's own `det`, carried into the bracket basis. -/
public theorem bracket_det : (st.t * st.s - st.r * st.u) * st.v = 1 := by
  grind only [t, u, st.det]

/-- `v` must be either `1` or `-1`. -/
public theorem v_cases : st.v = 1 ∨ st.v = -1 :=
  Int.eq_one_or_neg_one_of_mul_eq_one (Int.mul_comm _ st.v ▸ st.bracket_det)

/-- In particular, `v` is nonzero. -/
public theorem v_nonzero : st.v ≠ 0 := by grind only [st.v_cases]

/-! ## The residual `c` -/

/--
If `0 < b`, then the loop exit condition means that we stopped short of a full Euclidean
algorithm step, so `k < a/b`. Proof: we have `q + ks ≤ limit` from the definition of
`k`, and `limit < q + ⌊a/b⌋s` from the loop exit condition, so `k < ⌊a/b⌋`.

In both this case and the `b = 0` case we have `(k + 1)b ≤ a`.
-/
theorem k_upper : (st.k + 1) * st.b ≤ st.a := by
  rcases Int.lt_or_eq_of_le st.b_nonneg with hlt | heq
  · exact (Int.le_ediv_iff_mul_le hlt).mp (Int.lt_of_lt_mul_pos st.s_pos
      (by grind only [k, u, LoopState.loopCondition, st.exited, st.u_le_limit]))
  · grind only [st.b_lt_a, st.b_nonneg]

/-- `c` is defined to be `a` reduced by `k` copies of `b`. -/
public def c := st.a - st.k * st.b

/-- `c` is the cross-multiplied distance from `m/n` to `t/u`, oriented by `v`. -/
public theorem c_eq_tu_cross : (st.t * args.n - args.m * st.u) * st.v = st.c := by
  grind only [c, t, u, st.a_eq_pq_cross, st.b_eq_rs_cross]

/-- Since `(k + 1)b ≤ a`, we have `b ≤ c`. -/
public theorem b_le_c : st.b ≤ st.c := by grind only [c, st.k_upper]

/-- `c` is positive: follows from `0 ≤ b ≤ c`, `b < a` and the definition of `c`. -/
public theorem c_pos : 0 < st.c := by grind only [st.b_nonneg, c, st.b_le_c, st.b_lt_a]

/-! ## The return value -/

/-- `st.rv` is the return value from `limitDenominator` — either `r/s` or `t/u`. -/
@[expose] public def rv : Candidate args :=
    if 2 * st.b * st.u ≤ args.n then st.rs else st.tu

end PostLoopState

/-! # End to end -/

/-- The state on exit from the loop, run from the initial state. -/
@[expose] public def Arguments.postLoopState (args : Arguments) : PostLoopState args :=
  let loopState := LoopState.initialLoopState args
  ⟨loopState.runLoop, loopState.runLoop_loopCondition_false⟩

/-- The full algorithm, end to end. -/
@[expose] public def Arguments.limitDenominator (args : Arguments) : Candidate args :=
  args.postLoopState.rv
