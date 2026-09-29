module

public import LimitDenominator.Definitions.Specification
public import LimitDenominator.Proofs.Algorithm
public import LimitDenominator.Proofs.Arguments
public import LimitDenominator.Proofs.Candidate
import LimitDenominator.Proofs.IntLemmas
import LimitDenominator.Proofs.Optimality
import LimitDenominator.Proofs.Reduced

/-!
The rest of the analysis of the algorithm: the ambiguous and trivial cases, uniqueness
of best approximations, the residual staying positive, and the bridge to the
specification.
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

/-- Recovery of `n` from `a` and `b`. -/
theorem as_add_bq_eq_n : st.a * st.s + st.b * st.q = args.n := by
  grind only [st.a_eq_pq_cross, st.b_eq_rs_cross, st.det]

/-- Recovery of `m` from `b` and `c`. -/
theorem bt_add_cr_eq_m : st.b * st.t + st.c * st.r = args.m := by
  grind only [st.b_eq_rs_cross, st.c_eq_tu_cross, st.bracket_det]

/--
If `n ≤ limit` then `b = 0`. Proof: we have `bu + cs = n ≤ limit < s + u`, implying that
at least one of `b` and `c` is nonpositive. But we already know that `0 < c`.
-/
theorem b_eq_zero_of_n_le_limit (h : args.n ≤ args.limit) : st.b = 0 := by
  have lc : (1 - st.c) * st.s + (1 - st.b) * st.u > 0 :=
    by grind only [st.bu_add_cs_eq_n, st.limit_lt_s_add_u]
  grind only [st.b_nonneg, st.c_pos, Int.pos_or_pos_of_lincomb_pos st.s_pos st.u_pos lc]

/-- If `m` and `n` are coprime and `b = 0`, then `m = r` and `n = s`. -/
theorem mn_eq_rs_of_b_eq_zero (hmn : args.m.gcd args.n = 1) (hb : st.b = 0) :
    args.m = st.r ∧ args.n = st.s := by
  have : args.m = st.c * st.r ∧ args.n = st.c * st.s := by
    grind only [st.bt_add_cr_eq_m, st.bu_add_cs_eq_n]
  have : st.c = 1 := by
    apply Int.eq_one_of_dvd_one (Int.le_of_lt st.c_pos)
    apply Int.gcd_eq_one_iff.mp hmn st.c <;> grind only [Int.dvd_mul_right]
  grind only

/-! ## Distances -/

/-! ## The bracket -/

/-! ## Best approximations -/

variable {yz : Candidate args}

/-! ## Choosing between the two candidates -/

/-! ## The ambiguous case -/

section ambiguous

/-
This section studies the special case where the input `m/n` is a half integer
and `limit = 1`.
-/

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

end ambiguous

end PostLoopState

namespace Arguments

variable (args : Arguments)

/-! # Results -/

/-! ## Uniqueness of best approximations -/

/-- Outside the ambiguous case, any two best approximations are equal. -/
theorem non_ambiguous_best (not_amb : ¬ args.ambiguous) {ef gh : Candidate args}
    (hef : ef.best) (hgh : gh.best) : ef = gh := by
  let st := args.postLoopState
  cases st.eq_rs_or_eq_tu_of_best hef <;> cases st.eq_rs_or_eq_tu_of_best hgh
  <;> grind only [st.ambiguous_of_rs_and_tu_best]

/--
In the ambiguous case, the best approximations are exactly `⌊m/n⌋` and `⌊m/n⌋ + 1`.
-/
theorem ambiguous_best (hamb : args.ambiguous) {yz : Candidate args} :
    yz.best ↔ yz = args.floor ∨ yz = args.floorAddOne := by
  let st := args.postLoopState
  grind only [st.rs_best_and_tu_best hamb, st.endpoints_eq_floor_pair hamb,
    st.eq_rs_or_eq_tu_of_best]

/-! ## Any best approximation is reduced -/

/-! ## The trivial case -/

/--
In the trivial case `m/n` is a best approximation to itself.

Proved by running the loop anyway: with `n ≤ limit` the residual `b` is zero on exit, so
the exit state's `r/s` is `m/n` itself, and `r/s` is best.
-/
theorem self_best_of_trivial (h : args.trivial) :
    Candidate.best ⟨args.m, args.n, args.n_pos, h.2⟩ := by
  let st := args.postLoopState
  have best_rs : st.rs.best := by
    rw [st.rs_best_iff]
    grind only [Int.mul_pos st.c_pos st.s_pos, st.b_eq_zero_of_n_le_limit h.2]
  grind only [st.mn_eq_rs_of_b_eq_zero h.1 (st.b_eq_zero_of_n_le_limit h.2)]

/-! ## The return value -/

/-- In the ambiguous case, `⌊m/n⌋` is returned. -/
public theorem limitDenominator_ambiguous_case (hamb : args.ambiguous) :
    args.limitDenominator = args.floor :=
  args.postLoopState.rv_eq_floor hamb

end Arguments

/-! ## The residual stays positive -/

namespace LoopState

variable {args : Arguments} (st : LoopState args)

/-- If `st.b = 0` then `b` remains `0` after running the loop. -/
theorem runLoop_b_eq_zero (hst : st.b = 0) : st.runLoop.b = 0 := by
  fun_induction runLoop st <;> grind only [loopCondition]

/--
For a reduced target whose denominator exceeds the limit, the residual `b` stays
positive.

Proved by running the loop on from `st`: were `b` zero it would stay zero to exit, where
`mn_eq_rs_of_b_eq_zero` puts `n = s` within the limit.
-/
public theorem b_pos (hgcd : Int.gcd args.m args.n = 1) (hlim : args.limit < args.n) :
    0 < st.b := by
  let pst : PostLoopState args := ⟨st.runLoop, st.runLoop_loopCondition_false⟩
  refine Int.lt_iff_le_and_ne.mpr ⟨st.b_nonneg, ?_⟩; intro
  grind only [pst.s_le_limit,
    pst.mn_eq_rs_of_b_eq_zero hgcd (by grind only [st.runLoop_b_eq_zero])]

end LoopState

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

/--
A reduced target whose denominator is already within the limit is its own best
approximation: the fast path, which the shipped listing takes before its loop.
-/
public theorem isBestApproximation_self {m n l : Int} (hn : 0 < n) (hl : n ≤ l)
    (hgcd : Int.gcd m n = 1) : isBestApproximation m n l m n := by
  let args : Arguments := ⟨m, n, l, hn, by omega⟩
  exact (best_iff_isBestApproximation _).mp (args.self_best_of_trivial ⟨hgcd, hl⟩)
