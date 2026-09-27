module

public import LimitDenominator.Definitions.Specification
public import LimitDenominator.Proofs.Algorithm
public import LimitDenominator.Proofs.Arguments
public import LimitDenominator.Proofs.Candidate
import LimitDenominator.Proofs.IntLemmas

/-!
The analysis of the algorithm: the bracket on exit from the loop, which of its two
endpoints is best, the ambiguous case, and the bridge to the specification.
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

/--
We define `st.lev` as an orientation-aware less-than-or-equal-to relation:
`st.lev ef gh` means `e/f ≤ g/h` if `st.v = 1`, and `g/h ≤ e/f` if `st.v = -1`.
-/
def lev := ef.num * gh.den * st.v ≤ gh.num * ef.den * st.v

/--
`st.eqv` is defined analogously; since `v` is nonzero, it is equality of fractions
for either sign of `v`.
-/
def eqv := ef.num * gh.den * st.v = gh.num * ef.den * st.v

/-! ## The determinant -/

/-- The loop's own `det`, carried into the bracket basis. -/
theorem bracket_det : (st.t * st.s - st.r * st.u) * st.v = 1 := by
  grind only [t, u, st.det]

/-- `v` must be either `1` or `-1`. -/
theorem v_cases : st.v = 1 ∨ st.v = -1 :=
  Int.eq_one_or_neg_one_of_mul_eq_one (Int.mul_comm _ st.v ▸ st.bracket_det)

/-- In particular, `v` is nonzero. -/
theorem v_nonzero : st.v ≠ 0 := by grind only [st.v_cases]

/-- The pure candidate `r/s` is in lowest terms. -/
theorem isReduced_rs : st.rs.isReduced :=
  ⟨-st.u * st.v, st.t * st.v, by grind only [st.bracket_det]⟩

/-- The mixed candidate `t/u` likewise. -/
theorem isReduced_tu : st.tu.isReduced :=
  ⟨st.s * st.v, -st.r * st.v, by grind only [st.bracket_det]⟩

/-! ## Residuals -/

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
def c := st.a - st.k * st.b

/-- `c` is the cross-multiplied distance from `m/n` to `t/u`, oriented by `v`. -/
theorem c_eq_tu_cross : (st.t * args.n - args.m * st.u) * st.v = st.c := by
  grind only [c, t, u, st.a_eq_pq_cross, st.b_eq_rs_cross]

/-- Since `(k + 1)b ≤ a`, we have `b ≤ c`. -/
theorem b_le_c : st.b ≤ st.c := by grind only [c, st.k_upper]

/-- `c` is positive: follows from `0 ≤ b ≤ c`, `b < a` and the definition of `c`. -/
theorem c_pos : 0 < st.c := by grind only [st.b_nonneg, c, st.b_le_c, st.b_lt_a]

/-- One side of the bracket: `r/s ≤ m/n` when `v = 1`, and `m/n ≤ r/s` when `v = -1`. -/
theorem rs_lev_mn : st.r * args.n * st.v ≤ args.m * st.s * st.v := by
  grind only [st.b_eq_rs_cross, st.b_nonneg]

/-- The other side: `m/n ≤ t/u` when `v = 1`, and `t/u ≤ m/n` when `v = -1`. -/
theorem mn_lev_tu : args.m * st.u * st.v ≤ st.t * args.n * st.v := by
  grind only [st.c_eq_tu_cross, st.c_pos]

/-! ## Recovering the target -/

/-- Recovery of `m` from `b` and `c`. -/
theorem bt_add_cr_eq_m : st.b * st.t + st.c * st.r = args.m := by
  grind only [st.b_eq_rs_cross, st.c_eq_tu_cross, st.bracket_det]

/-- Recovery of `n` from `b` and `c`. -/
theorem bu_add_cs_eq_n : st.b * st.u + st.c * st.s = args.n := by
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

/-- Distance to a candidate beyond `r/s`, with the orientation supplying the sign. -/
theorem dist_of_lev_rs {ef : Candidate args} (h : st.lev ef st.rs) :
    ef.dist = (args.m * ef.den - ef.num * args.n) * st.v := by
  have rhs_nonneg : 0 ≤ (args.m * ef.den - ef.num * args.n) * st.v :=
    Int.le_of_le_mul_pos st.s_pos (by grind only [
      Int.le_mul_pos args.n_pos h, Int.le_mul_pos ef.den_pos st.rs_lev_mn])
  grind only [Candidate.dist, Int.abs_eq _ rhs_nonneg, st.v_cases]

/-- Distance of `r/s`. -/
theorem dist_rs : st.rs.dist = (args.m * st.s - st.r * args.n) * st.v :=
  st.dist_of_lev_rs Int.le_rfl

/-- Distance to a candidate beyond `t/u`, likewise. -/
theorem dist_of_tu_lev {ef : Candidate args} (h : st.lev st.tu ef) :
    ef.dist = (ef.num * args.n - args.m * ef.den) * st.v := by
  have rhs_nonneg : 0 ≤ (ef.num * args.n - args.m * ef.den) * st.v :=
    Int.le_of_le_mul_pos st.u_pos (by grind only [
      Int.le_mul_pos ef.den_pos st.mn_lev_tu, Int.le_mul_pos args.n_pos h])
  grind only [Candidate.dist, Int.abs_eq _ rhs_nonneg, st.v_cases]

/-- Distance of `t/u`. -/
theorem dist_tu : st.tu.dist = (st.t * args.n - args.m * st.u) * st.v :=
  st.dist_of_tu_lev Int.le_rfl

/-! ## The bracket -/

/-- A candidate lies outside the bracket, or at one of its endpoints. -/
theorem lev_rs_or_tu_lev (yz : Candidate args) :
    st.lev yz st.rs ∨ st.lev st.tu yz := by
  have lc : 0 < (1 - (st.t * yz.den - yz.num * st.u) * st.v) * st.s
      + (1 - (yz.num * st.s - st.r * yz.den) * st.v) * st.u := by
    grind only [
      Int.eq_mul_pos yz.den_pos st.bracket_det, st.limit_lt_s_add_u, yz.den_limited]
  cases Int.pos_or_pos_of_lincomb_pos st.s_pos st.u_pos lc
  · right; grind only [lev]
  · left; grind only [lev]

/-- If `y/z = r/s` then `s ≤ z` (because `r/s` is in lowest terms). -/
theorem den_le_of_eqv_rs {yz : Candidate args} (yz_eqv_rs : st.eqv yz st.rs) :
    st.s ≤ yz.den := by
  have : yz.den = st.s * ((st.t * yz.den - yz.num * st.u) * st.v) := by
    grind only [
      Int.eq_mul_pos st.u_pos yz_eqv_rs, Int.eq_mul_pos yz.den_pos st.bracket_det]
  exact this ▸ Int.divisor_le_mul (this ▸ yz.den_pos)

/-- If `y/z = t/u` then `u ≤ z` (because `t/u` is in lowest terms). -/
theorem den_le_of_tu_eqv {yz : Candidate args} (tu_eqv_yz : st.eqv st.tu yz) :
    st.u ≤ yz.den := by
  have : yz.den = st.u * ((yz.num * st.s - st.r * yz.den) * st.v) := by
    grind only [
      Int.eq_mul_pos st.s_pos tu_eqv_yz, Int.eq_mul_pos yz.den_pos st.bracket_det]
  exact this ▸ Int.divisor_le_mul (this ▸ yz.den_pos)

/-- `r/s` is at least as good as anything beyond it. -/
theorem better_rs_of_lev {yz : Candidate args} (h : st.lev yz st.rs) :
    st.rs.better yz := by
  unfold Candidate.better
  rw [st.dist_rs, st.dist_of_lev_rs h]
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · left; grind only [Int.lt_mul_pos args.n_pos hlt]
  · right; exact ⟨by grind only [Int.eq_mul_pos args.n_pos], st.den_le_of_eqv_rs heq⟩

/-- `t/u` is at least as good as anything beyond it. -/
theorem better_tu_of_lev {yz : Candidate args} (h : st.lev st.tu yz) :
    st.tu.better yz := by
  unfold Candidate.better
  rw [st.dist_tu, st.dist_of_tu_lev h]
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · left; grind only [Int.lt_mul_pos args.n_pos hlt]
  · right; exact ⟨by grind only [Int.eq_mul_pos args.n_pos], st.den_le_of_tu_eqv heq⟩

/-- One of the two endpoints is at least as good as any candidate. -/
theorem better_rs_or_better_tu (yz : Candidate args) :
    st.rs.better yz ∨ st.tu.better yz :=
  (st.lev_rs_or_tu_lev yz).imp st.better_rs_of_lev st.better_tu_of_lev

/-! ## Best approximations -/

variable {yz : Candidate args}

/-- A best approximation beyond `r/s` is `r/s` itself. -/
theorem eq_rs_of_lev_of_best (h : st.lev yz st.rs) (yz_best : yz.best) :
    yz = st.rs := by
  have yz_rs : yz.better st.rs := yz_best st.rs
  unfold Candidate.better at yz_rs
  rw [st.dist_rs, st.dist_of_lev_rs h] at yz_rs
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · -- y/z < r/s makes r/s strictly better than y/z, contradicting yz_rs
    grind only [Int.lt_mul_pos args.n_pos hlt]
  · -- y/z = r/s as fractions, so s ≤ z; yz_rs gives z ≤ s
    have ⟨_, z_le_s⟩ :=
      Or.resolve_left yz_rs (by grind only [Int.eq_mul_pos args.n_pos heq])
    exact Candidate.eq_of_den_eq_of_cross_eq
      (Int.le_antisymm z_le_s (st.den_le_of_eqv_rs heq))
      (Int.eq_of_mul_eq_mul_right st.v_nonzero heq)

/-- A best approximation beyond `t/u` is `t/u` itself. -/
theorem eq_tu_of_lev_of_best (h : st.lev st.tu yz) (yz_best : yz.best) :
    yz = st.tu := by
  have yz_tu : yz.better st.tu := yz_best st.tu
  unfold Candidate.better at yz_tu
  rw [st.dist_tu, st.dist_of_tu_lev h] at yz_tu
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · -- t/u < y/z makes t/u strictly better than y/z, contradicting yz_tu
    grind only [Int.lt_mul_pos args.n_pos hlt]
  · -- y/z = t/u as fractions, so u ≤ z; yz_tu gives z ≤ u
    have ⟨_, z_le_u⟩ :=
      Or.resolve_left yz_tu (by grind only [Int.eq_mul_pos args.n_pos heq])
    exact Candidate.eq_of_den_eq_of_cross_eq
      (Int.le_antisymm z_le_u (st.den_le_of_tu_eqv heq))
      (Int.eq_of_mul_eq_mul_right st.v_nonzero heq.symm)

/-- Any best approximation is equal to either `r/s` or `t/u`. -/
theorem eq_rs_or_eq_tu_of_best (yz_best : yz.best) :
    yz = st.rs ∨ yz = st.tu :=
  (st.lev_rs_or_tu_lev yz).imp (st.eq_rs_of_lev_of_best · yz_best)
    (st.eq_tu_of_lev_of_best · yz_best)

/-- `r/s` is best iff `bu < cs` or `bu = cs` and `s ≤ u`. -/
theorem rs_best_iff : st.rs.best ↔
    st.b * st.u < st.c * st.s ∨ st.b * st.u = st.c * st.s ∧ st.s ≤ st.u := by
  have : st.rs.best ↔ st.rs.better st.tu :=
    ⟨(· st.tu), fun h yz =>
      (st.better_rs_or_better_tu yz).elim id (Candidate.better_trans h)⟩
  grind only [
    Candidate.better, st.dist_rs, st.dist_tu, st.b_eq_rs_cross, st.c_eq_tu_cross]

/-- `t/u` is best iff `cs < bu` or `cs = bu` and `u ≤ s`. -/
theorem tu_best_iff : st.tu.best ↔
    st.c * st.s < st.b * st.u ∨ st.c * st.s = st.b * st.u ∧ st.u ≤ st.s := by
  have : st.tu.best ↔ st.tu.better st.rs :=
    ⟨(· st.rs), fun h yz =>
      (st.better_rs_or_better_tu yz).elim (Candidate.better_trans h) id⟩
  grind only [
    Candidate.better, st.dist_tu, st.dist_rs, st.c_eq_tu_cross, st.b_eq_rs_cross]

/-! ## Choosing between the two candidates -/

/-- If `bu = cs` then it follows from `b ≤ c` that `s ≤ u`. -/
theorem s_le_u_of_bu_eq_cs (h : st.b * st.u = st.c * st.s) : st.s ≤ st.u :=
  Int.le_of_le_mul_pos st.c_pos (by grind only [Int.le_mul_pos st.u_pos st.b_le_c])

/-- The returned candidate is a best approximation. -/
theorem rv_best : st.rv.best := by
  have := st.bu_add_cs_eq_n
  unfold rv; split
  · rcases Int.lt_or_eq_of_le (show st.b * st.u ≤ st.c * st.s by grind only)
      with hlt | heq
    · exact st.rs_best_iff.mpr (.inl hlt)
    · exact st.rs_best_iff.mpr (.inr ⟨heq, st.s_le_u_of_bu_eq_cs heq⟩)
  · exact st.tu_best_iff.mpr (.inl (by grind only))

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
  -- With `s = u = 1`: `bu = cs` gives `b = c = a - kb`, so `kb = a - b > 0`, and
  -- `q = 1 - k ≥ 0`.
  have kb_pos : 0 < st.k * st.b := by
    grind only [c, st.b_lt_a, st.bu_eq_cs hamb, st.s_eq_one_and_u_eq_one hamb]
  exact st.v_eq_one_of_q_eq_zero (by grind only [
    u, st.q_nonneg, st.b_nonneg, st.s_eq_one_and_u_eq_one hamb,
    Int.mul_pos_iff.mp kb_pos])

/-- In the ambiguous case `⌊m/n⌋` is returned. -/
theorem rv_eq_floor : st.rv = args.floor := by
  have : st.rv = st.rs := ite_eq_left (by grind only [st.bu_eq_cs, st.bu_add_cs_eq_n])
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

/--
A best approximation is one of the two bracket endpoints, and both of those are in
lowest terms.
-/
theorem isReduced_of_best {ef : Candidate args} (hef : ef.best) :
    ef.isReduced := by
  let st := args.postLoopState
  rcases st.eq_rs_or_eq_tu_of_best hef with rfl | rfl
  · exact st.isReduced_rs
  · exact st.isReduced_tu

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

/-- The `limitDenominator` return value is always a best approximation. -/
public theorem limitDenominator_best : args.limitDenominator.best :=
  args.postLoopState.rv_best

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
For a target in lowest terms whose denominator exceeds the limit, the residual `b` stays
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
  ⟨fun hbest => ⟨ef.den_pos, ef.den_limited, fun y z hz hzl => hbest ⟨y, z, hz, hzl⟩⟩,
    fun ⟨_, _, hall⟩ gh => hall gh.num gh.den gh.den_pos gh.den_limited⟩

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
The result is in lowest terms, and that is a consequence of the specification rather
than a part of it.

A pair satisfying the specification is one of the two bracket endpoints, and the
bracket's determinant is a Bézout identity for each of them.
-/
public theorem isBestApproximation.gcd_eq_one {m n l r s : Int} (hn : 0 < n)
    (h : isBestApproximation m n l r s) : Int.gcd r s = 1 := by
  have hl : 1 ≤ l := by have := h.1; have := h.2.1; omega
  let args : Arguments := ⟨m, n, l, hn, hl⟩
  let ef : Candidate args := ⟨r, s, h.1, h.2.1⟩
  obtain ⟨g, k, hb⟩ := args.isReduced_of_best ((best_iff_isBestApproximation ef).mpr h)
  exact Int.gcd_eq_one_of_bezout hb

/--
A target in lowest terms whose denominator is already within the limit is its own best
approximation: the fast path, which the shipped listing takes before its loop.
-/
public theorem isBestApproximation_self {m n l : Int} (hn : 0 < n) (hl : n ≤ l)
    (hgcd : Int.gcd m n = 1) : isBestApproximation m n l m n := by
  let args : Arguments := ⟨m, n, l, hn, by omega⟩
  exact (best_iff_isBestApproximation _).mp (args.self_best_of_trivial ⟨hgcd, hl⟩)
