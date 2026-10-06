module

public import LimitDenominator.Proofs.Arguments
public import LimitDenominator.Proofs.Candidate
import LimitDenominator.Proofs.IntLemmas

/-!
This module defines the `limitDenominator` algorithm and structures representing
the loop state (with its invariants) and the post-loop state (with some basic
consequences).
-/

/-! # The loop -/

/-! ## Loop state and loop invariants -/

/--
The `LoopState` structure captures the loop state and the loop invariants.
-/
public structure LoopState (args : Arguments) where
  /-- The larger of the two most recent Euclidean remainders. -/
  a : Int
  /-- The smaller of the two most recent Euclidean remainders. -/
  b : Int
  /-- Numerator of the previous convergent. -/
  p : Int
  /-- Denominator of the previous convergent. -/
  q : Int
  /-- Numerator of the most recent convergent. -/
  r : Int
  /-- Denominator of the most recent convergent. -/
  s : Int
  /-- The orientation. -/
  v : Int
  /- The loop invariants. -/
  b_nonneg : 0 ≤ b
  b_lt_a : b < a
  q_nonneg : 0 ≤ q
  s_pos : 0 < s
  s_le_limit : s ≤ args.limit
  det : (p * s - r * q) * v = 1
  a_eq_pq_cross : (p * args.n - args.m * q) * v = a
  b_eq_rs_cross : (args.m * s - r * args.n) * v = b

/-! ## Loop condition, initial loop state, and loop body -/

/-- The state before the first iteration. -/
@[expose] public def Arguments.initialLoopState (args : Arguments) :
    LoopState args where
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

namespace LoopState

variable {args : Arguments} (st : LoopState args)

/-- Condition guarding iteration of the while loop. -/
@[expose] public def loopCondition := 0 < st.b ∧ st.q + st.a / st.b * st.s ≤ args.limit

/-- The loop condition is decidable. -/
public instance : Decidable st.loopCondition := by unfold loopCondition; infer_instance

/--
The state resulting from execution of the loop body on a state satisfying the loop
condition.
-/
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

/-- The termination measure for the loop: `a` as a `Nat`. -/
public def loopMeasure : Nat := st.a.toNat

/-- `nextLoopState` reduces the measure. -/
theorem loopMeasure_decreasing (hst : st.loopCondition) :
    (st.nextLoopState hst).loopMeasure < st.loopMeasure :=
  (Int.toNat_lt_toNat (Int.lt_of_le_of_lt st.b_nonneg st.b_lt_a)).mpr st.b_lt_a

/-! ## Additional loop invariants -/

/-- `v` must be either `1` or `-1`. -/
public theorem v_cases : st.v = 1 ∨ st.v = -1 :=
  Int.eq_one_or_neg_one_of_mul_eq_one (Int.mul_comm _ st.v ▸ st.det)

/-- In particular, `v` is nonzero. -/
public theorem v_nonzero : st.v ≠ 0 := by grind only [st.v_cases]

end LoopState

/-! # On exit from the loop -/

/-
Here we build the post-loop quantities, in particular the *mixed* candidate `t/u` that
provides our second bracket endpoint (alongside the *pure* candidate `r/s` from the
loop).
-/

/-- `PostLoopState` represents the state on exiting the loop. -/
public structure PostLoopState (args : Arguments) extends LoopState args where
  /-- Proof that the loop condition is false. -/
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
From the definition of `k` we have `limit - q < ks + s`, giving `limit < s + u`.
-/
public theorem limit_lt_s_add_u : args.limit < st.s + st.u := by
  grind only [k, u, Int.lt_ediv_mul (args.limit - st.q) st.s_pos]

/-- Since `s ≤ limit < s + u`, it follows that `0 < u`. -/
public theorem u_pos : 0 < st.u := by grind only [st.s_le_limit, st.limit_lt_s_add_u]

/-- The mixed candidate `t/u`, packaged as a `Candidate`. -/
public abbrev tu : Candidate args := ⟨st.t, st.u, st.u_pos, st.u_le_limit⟩

/-! ## The residual `c` and post-loop identities -/

/-- `c` is defined to be `a` reduced by `k` copies of `b`. -/
public def c := st.a - st.k * st.b

/-- The loop's own `det`, carried into the bracket basis. -/
public theorem bracket_det : (st.t * st.s - st.r * st.u) * st.v = 1 := by
  grind only [t, u, st.det]

/-- `c` is the cross-multiplied distance from `m/n` to `t/u`, oriented by `v`. -/
public theorem c_eq_tu_cross : (st.t * args.n - args.m * st.u) * st.v = st.c := by
  grind only [c, t, u, st.a_eq_pq_cross, st.b_eq_rs_cross]

/-- Recovery of `m` from `b` and `c`. -/
public theorem bt_add_cr_eq_m : st.b * st.t + st.c * st.r = args.m := by
  grind only [st.b_eq_rs_cross, st.c_eq_tu_cross, st.bracket_det]

/-- Recovery of `n` from `b` and `c`. -/
public theorem bu_add_cs_eq_n : st.b * st.u + st.c * st.s = args.n := by
  grind only [st.b_eq_rs_cross, st.c_eq_tu_cross, st.bracket_det]

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

/-- Since `(k + 1)b ≤ a`, we have `b ≤ c`. -/
public theorem b_le_c : st.b ≤ st.c := by grind only [c, st.k_upper]

/-- `c` is positive: follows from `0 ≤ b ≤ c`, `b < a` and the definition of `c`. -/
public theorem c_pos : 0 < st.c := by grind only [st.b_nonneg, c, st.b_le_c, st.b_lt_a]

/-! ## The return value -/

/-- `st.rv` is the return value from `limitDenominator` — either `r/s` or `t/u`. -/
@[expose] public def rv : Candidate args :=
    if 2 * st.b * st.u ≤ args.n then st.rs else st.tu

end PostLoopState

/-! # End-to-end execution; definition of `limitDenominator` -/

namespace LoopState

/-- Run the loop to completion from a given state. -/
@[expose] public def runLoop {args : Arguments} (st : LoopState args) :
    PostLoopState args :=
  if h : st.loopCondition then runLoop (st.nextLoopState h) else ⟨st, h⟩
termination_by st.loopMeasure
decreasing_by exact st.loopMeasure_decreasing h

end LoopState

namespace Arguments

variable (args : Arguments)

/-- The state on exit from the loop, run from the initial state. -/
@[expose] public def postLoopState : PostLoopState args := args.initialLoopState.runLoop

/-- The full algorithm, end to end. -/
@[expose] public def limitDenominator : Candidate args := args.postLoopState.rv

end Arguments
