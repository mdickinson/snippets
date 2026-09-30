module

public import LimitDenominator.Proofs.Algorithm
public import LimitDenominator.Proofs.Arguments
public import LimitDenominator.Proofs.Candidate
import LimitDenominator.Proofs.BaseAnalysis
import LimitDenominator.Proofs.IntLemmas

/-!
When the best approximation is unique: always, except in the *ambiguous* case, where
`⌊m/n⌋` and `⌊m/n⌋ + 1` are both best and the algorithm returns `⌊m/n⌋`.
-/

/-! ## The ambiguous case -/

namespace Arguments

/--
A set of arguments is *ambiguous* if the limit is `1` and `m/n` is a half-integer, that
is, `m/n = w + 1/2` for some integer `w`.
-/
@[expose] public def ambiguous (args : Arguments) :=
  args.limit = 1 ∧ ∃ (w : Int), 2 * args.m = (2 * w + 1) * args.n

/-- If `m/n = w + 1/2` then `⌊m/n⌋ = w`. -/
theorem floor_eq_of_half_integer (args : Arguments) {w : Int}
    (hw : 2 * args.m = (2 * w + 1) * args.n) : args.m / args.n = w :=
  (Int.ediv_eq_iff_of_pos args.n_pos).mpr (by grind only [args.n_pos])

/-- `⌊m/n⌋` as a candidate. -/
@[expose] public def floor (args : Arguments) : Candidate args :=
  ⟨args.m / args.n, 1, by decide, args.one_le_limit⟩

/-- `⌊m/n⌋ + 1` as a candidate. -/
@[expose] public def floorAddOne (args : Arguments) : Candidate args :=
  ⟨args.m / args.n + 1, 1, by decide, args.one_le_limit⟩

end Arguments

/-! ## The endpoints in the ambiguous case -/

namespace PostLoopState

variable {args : Arguments} (st : PostLoopState args)

/-- Oriented version of the ambiguous condition. -/
theorem ambiguous_iff_oriented : args.ambiguous ↔
    args.limit = 1 ∧ ∃ (w : Int), 2 * args.m * st.v = (2 * w * st.v + 1) * args.n := by
  unfold Arguments.ambiguous
  rcases st.v_cases with hv | hv <;> rw [hv] <;> refine and_congr_right fun _ => ?_
  · simp
  · exact ⟨fun ⟨w, hw⟩ => ⟨w + 1, by grind only⟩,
      fun ⟨w, hw⟩ => ⟨w - 1, by grind only⟩⟩

/-- If both `r/s` and `t/u` are best approximations then we're in the ambiguous case. -/
theorem ambiguous_of_rs_and_tu_best
    (rs_best : st.rs.best) (tu_best : st.tu.best) : args.ambiguous := by
  rw [st.ambiguous_iff_oriented]
  cases (show st.rs.better st.tu from rs_best st.tu)
  <;> cases (show st.tu.better st.rs from tu_best st.rs) <;> try omega
  have : (st.t - st.r) * st.v * st.s = 1 := by grind only [st.bracket_det]
  have : st.s = 1 := by grind only [Int.eq_one_of_mul_eq_one_left]
  exact ⟨by grind only [args.one_le_limit, st.limit_lt_s_add_u], st.r,
    by grind only [st.dist_rs, st.dist_tu]⟩

/- From this point on assume that we're in the ambiguous case. -/
variable (hamb : args.ambiguous)
include hamb

/-- In the ambiguous case `s = u = 1`, both being bounded by a limit of `1`. -/
theorem s_eq_one_and_u_eq_one : st.s = 1 ∧ st.u = 1 := by
  grind only [hamb.1, st.s_le_limit, st.s_pos, st.u_le_limit, st.u_pos]

/--
Collected consequences of ambiguity: `bu = cs`, `r/s v + 1/2 = m/n v = t/u v - 1/2`.
-/
theorem consequences_of_ambiguity : st.b * st.u = st.c * st.s
    ∧ 2 * args.m * st.s * st.v = (2 * st.r * st.v + st.s) * args.n
    ∧ 2 * args.m * st.u * st.v = (2 * st.t * st.v - st.u) * args.n := by
  obtain ⟨w, hw⟩ := (st.ambiguous_iff_oriented.mp hamb).2
  have := st.s_eq_one_and_u_eq_one hamb
  have : 2 * st.b * st.u = 2 * (w - st.r * st.u) * st.v * args.n + args.n := by
    grind only [Int.eq_mul_pos st.u_pos st.b_eq_rs_cross]
  have : 2 * st.c * st.s = 2 * (st.t * st.s - w) * st.v * args.n - args.n := by
    grind only [Int.eq_mul_pos st.s_pos st.c_eq_tu_cross]
  -- `0 ≤ b` and `0 < c` place `wv` in `[ruv, tsv)`, an interval of length one by
  -- `bracket_det`, so `wv = ruv`.
  have : 0 < 2 * (st.t * st.s * st.v - w * st.v) - 1 :=
    Int.lt_of_lt_mul_pos args.n_pos (by grind only [Int.mul_pos st.c_pos st.s_pos])
  have : 0 ≤ 2 * (w * st.v - st.r * st.u * st.v) + 1 :=
    Int.le_of_le_mul_pos args.n_pos
      (by grind only [Int.mul_nonneg st.b_nonneg (Int.le_of_lt st.u_pos)])
  have : st.t * st.s * st.v - st.r * st.u * st.v = 1 := by grind only [st.bracket_det]
  have : w * st.v - st.r * st.u * st.v = 0 := by omega
  grind only

/-- In the ambiguous case, `bu = cs`. -/
theorem bu_eq_cs : st.b * st.u = st.c * st.s := (st.consequences_of_ambiguity hamb).1

/-- Both `r/s` and `t/u` are best approximations. -/
theorem rs_best_and_tu_best : st.rs.best ∧ st.tu.best := by
  grind only [
    st.rs_best_iff, st.tu_best_iff, st.bu_eq_cs hamb, st.s_eq_one_and_u_eq_one hamb]

/--
The two endpoints are `⌊m/n⌋/1` and `(⌊m/n⌋ + 1)/1`: in that order when `v = 1`, and
swapped when `v = -1`.
-/
theorem endpoints_eq_floor_pair :
    st.v = 1 ∧ st.rs = args.floor ∧ st.tu = args.floorAddOne
    ∨ st.v = -1 ∧ st.rs = args.floorAddOne ∧ st.tu = args.floor := by
  rcases st.v_cases with hv | hv
  · left; grind only [
      Arguments.floor, Arguments.floorAddOne, st.s_eq_one_and_u_eq_one hamb,
      st.bracket_det, st.consequences_of_ambiguity hamb,
      args.floor_eq_of_half_integer (w := st.r)]
  · right; grind only [
      Arguments.floor, Arguments.floorAddOne, st.s_eq_one_and_u_eq_one hamb,
      st.bracket_det, st.consequences_of_ambiguity hamb,
      args.floor_eq_of_half_integer (w := st.t)]

/-- In the ambiguous case, `v = 1`. -/
theorem v_eq_one : st.v = 1 := by
  -- `as + bq` and `bu + cs` are both `n`. With `s = u = 1` and `b = c` that reads
  -- `a + bq = 2b`, so `(1 - q)b = a - b` is positive, so `q < 1`, and `q = 0`.
  have : 0 < (1 - st.q) * st.b := by grind only [st.b_lt_a, st.as_add_bq_eq_n,
    st.bu_add_cs_eq_n, st.bu_eq_cs hamb, st.s_eq_one_and_u_eq_one hamb]
  exact st.v_eq_one_of_q_eq_zero
    (by grind only [st.q_nonneg, st.b_nonneg, Int.mul_pos_iff.mp this])

/-- In the ambiguous case `⌊m/n⌋` is returned. -/
theorem rv_eq_floor : st.rv = args.floor := by
  have : st.rv = st.rs :=
    st.rv_eq_ite_bu_le_cs ▸ ite_eq_left (Int.le_of_eq (st.bu_eq_cs hamb))
  grind only [st.v_eq_one hamb, st.endpoints_eq_floor_pair hamb]

end PostLoopState

/-! ## Uniqueness -/

namespace Arguments

/-- Outside the ambiguous case, any two best approximations are equal. -/
public theorem non_ambiguous_best (args : Arguments) (not_amb : ¬ args.ambiguous)
    {ef gh : Candidate args} (hef : ef.best) (hgh : gh.best) : ef = gh := by
  let st := args.postLoopState
  cases st.eq_rs_or_eq_tu_of_best hef <;> cases st.eq_rs_or_eq_tu_of_best hgh
  <;> grind only [st.ambiguous_of_rs_and_tu_best]

/--
In the ambiguous case, the best approximations are exactly `⌊m/n⌋` and `⌊m/n⌋ + 1`.
-/
public theorem ambiguous_best (args : Arguments) (hamb : args.ambiguous)
    {yz : Candidate args} : yz.best ↔ yz = args.floor ∨ yz = args.floorAddOne := by
  let st := args.postLoopState
  grind only [st.rs_best_and_tu_best hamb, st.endpoints_eq_floor_pair hamb,
    st.eq_rs_or_eq_tu_of_best]

/-- In the ambiguous case, `⌊m/n⌋` is returned. -/
public theorem limitDenominator_ambiguous_case (args : Arguments)
    (hamb : args.ambiguous) : args.limitDenominator = args.floor :=
  args.postLoopState.rv_eq_floor hamb

end Arguments
