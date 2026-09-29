module

public import LimitDenominator.Proofs.Algorithm
public import LimitDenominator.Proofs.Arguments
public import LimitDenominator.Proofs.Candidate
import LimitDenominator.Proofs.IntLemmas

/-!
The analysis of the algorithm for an arbitrary target: on exit from the loop the pure
and mixed candidates bracket the target, the returned one is a best approximation, and
every best approximation is one of the two.
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

/-! ## The bracket -/

/-- One side of the bracket: `r/s ≤ m/n` when `v = 1`, and `m/n ≤ r/s` when `v = -1`. -/
theorem rs_lev_mn : st.r * args.n * st.v ≤ args.m * st.s * st.v := by
  grind only [st.b_eq_rs_cross, st.b_nonneg]

/-- The other side: `m/n ≤ t/u` when `v = 1`, and `t/u ≤ m/n` when `v = -1`. -/
theorem mn_lev_tu : args.m * st.u * st.v ≤ st.t * args.n * st.v := by
  grind only [st.c_eq_tu_cross, st.c_pos]

/--
A candidate lies outside the bracket, or at one of its endpoints: anything strictly
inside has denominator at least `s + u`, which exceeds the limit.
-/
theorem lev_rs_or_tu_lev (yz : Candidate args) :
    st.lev yz st.rs ∨ st.lev st.tu yz := by
  have lc : 0 < (1 - (st.t * yz.den - yz.num * st.u) * st.v) * st.s
      + (1 - (yz.num * st.s - st.r * yz.den) * st.v) * st.u := by
    grind only [
      Int.eq_mul_pos yz.den_pos st.bracket_det, st.limit_lt_s_add_u, yz.den_limited]
  cases Int.pos_or_pos_of_lincomb_pos st.s_pos st.u_pos lc <;> grind only [lev]

/-! ## Distances -/

/-- Distance to a candidate beyond `r/s`, with the orientation supplying the sign. -/
theorem dist_of_lev_rs {ef : Candidate args} (h : st.lev ef st.rs) :
    ef.dist = (args.m * ef.den - ef.num * args.n) * st.v := by
  have rhs_nonneg : 0 ≤ (args.m * ef.den - ef.num * args.n) * st.v :=
    Int.le_of_le_mul_pos st.s_pos (by grind only [
      Int.le_mul_pos args.n_pos h, Int.le_mul_pos ef.den_pos st.rs_lev_mn])
  grind only [Candidate.dist, Int.abs_eq _ rhs_nonneg, st.v_cases]

/-- Distance of `r/s`. -/
public theorem dist_rs : st.rs.dist = (args.m * st.s - st.r * args.n) * st.v :=
  st.dist_of_lev_rs Int.le_rfl

/-- Distance to a candidate beyond `t/u`, likewise. -/
theorem dist_of_tu_lev {ef : Candidate args} (h : st.lev st.tu ef) :
    ef.dist = (ef.num * args.n - args.m * ef.den) * st.v := by
  have rhs_nonneg : 0 ≤ (ef.num * args.n - args.m * ef.den) * st.v :=
    Int.le_of_le_mul_pos st.u_pos (by grind only [
      Int.le_mul_pos ef.den_pos st.mn_lev_tu, Int.le_mul_pos args.n_pos h])
  grind only [Candidate.dist, Int.abs_eq _ rhs_nonneg, st.v_cases]

/-- Distance of `t/u`. -/
public theorem dist_tu : st.tu.dist = (st.t * args.n - args.m * st.u) * st.v :=
  st.dist_of_tu_lev Int.le_rfl

/-! ## Beyond an endpoint -/

variable {yz : Candidate args}

/-- `r/s` is better than anything beyond it. -/
theorem better_rs_of_lev (h : st.lev yz st.rs) : st.rs.better yz := by
  unfold Candidate.better; rw [st.dist_rs, st.dist_of_lev_rs h]
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · left; grind only [Int.lt_mul_pos args.n_pos hlt]
  · right; refine ⟨by grind only [Int.eq_mul_pos args.n_pos heq],
      Int.le_of_dvd yz.den_pos ⟨(st.t * yz.den - yz.num * st.u) * st.v, ?_⟩⟩
    grind only [Int.eq_mul_pos st.u_pos heq, Int.eq_mul_pos yz.den_pos st.bracket_det]

/-- `t/u` is better than anything beyond it. -/
theorem better_tu_of_lev (h : st.lev st.tu yz) : st.tu.better yz := by
  unfold Candidate.better; rw [st.dist_tu, st.dist_of_tu_lev h]
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · left; grind only [Int.lt_mul_pos args.n_pos hlt]
  · right; refine ⟨by grind only [Int.eq_mul_pos args.n_pos heq],
      Int.le_of_dvd yz.den_pos ⟨(yz.num * st.s - st.r * yz.den) * st.v, ?_⟩⟩
    grind only [Int.eq_mul_pos st.s_pos heq, Int.eq_mul_pos yz.den_pos st.bracket_det]

/-- One of the two endpoints is at least as good as any candidate. -/
theorem better_rs_or_better_tu (yz : Candidate args) :
    st.rs.better yz ∨ st.tu.better yz :=
  (st.lev_rs_or_tu_lev yz).imp st.better_rs_of_lev st.better_tu_of_lev

/-! ## Best approximations -/

/-- A best approximation beyond `r/s` is `r/s` itself. -/
theorem eq_rs_of_lev_of_best (h : st.lev yz st.rs) (yz_best : yz.best) :
    yz = st.rs := by
  cases st.better_rs_of_lev h <;> cases yz_best st.rs <;> try omega
  exact Candidate.eq_of_den_eq_of_cross_eq (by grind only)
    (Int.eq_of_eq_mul_pos args.n_pos (Int.eq_of_mul_eq_mul_right st.v_nonzero
      (by grind only [st.dist_rs, st.dist_of_lev_rs h])))

/-- A best approximation beyond `t/u` is `t/u` itself. -/
theorem eq_tu_of_lev_of_best (h : st.lev st.tu yz) (yz_best : yz.best) :
    yz = st.tu := by
  cases st.better_tu_of_lev h <;> cases yz_best st.tu <;> try omega
  exact Candidate.eq_of_den_eq_of_cross_eq (by grind only)
    (Int.eq_of_eq_mul_pos args.n_pos (Int.eq_of_mul_eq_mul_right st.v_nonzero
      (by grind only [st.dist_tu, st.dist_of_tu_lev h])))

/-- Any best approximation is equal to either `r/s` or `t/u`. -/
public theorem eq_rs_or_eq_tu_of_best (yz_best : yz.best) :
    yz = st.rs ∨ yz = st.tu :=
  (st.lev_rs_or_tu_lev yz).imp (st.eq_rs_of_lev_of_best · yz_best)
    (st.eq_tu_of_lev_of_best · yz_best)

/-- If `bu = cs` then it follows from `b ≤ c` that `s ≤ u`. -/
theorem s_le_u_of_bu_eq_cs (h : st.b * st.u = st.c * st.s) : st.s ≤ st.u :=
  Int.le_of_le_mul_pos st.c_pos (by grind only [Int.le_mul_pos st.u_pos st.b_le_c])

/-- `r/s` is best iff `bu ≤ cs`. -/
public theorem rs_best_iff : st.rs.best ↔ st.b * st.u ≤ st.c * st.s := by
  have hbest : st.rs.best ↔ st.rs.better st.tu :=
    ⟨(· st.tu), fun h yz =>
      (st.better_rs_or_better_tu yz).elim id (Candidate.better_trans h)⟩
  have := st.s_le_u_of_bu_eq_cs
  simp only [hbest, Candidate.better, st.dist_rs, st.dist_tu, st.b_eq_rs_cross,
    st.c_eq_tu_cross]
  omega

/-- `t/u` is best iff `cs < bu` or `cs = bu` and `s = u`. -/
public theorem tu_best_iff : st.tu.best ↔
    st.c * st.s < st.b * st.u ∨ st.c * st.s = st.b * st.u ∧ st.s = st.u := by
  have hbest : st.tu.best ↔ st.tu.better st.rs :=
    ⟨(· st.rs), fun h yz =>
      (st.better_rs_or_better_tu yz).elim (Candidate.better_trans h) id⟩
  have := st.s_le_u_of_bu_eq_cs
  simp only [hbest, Candidate.better, st.dist_tu, st.dist_rs, st.c_eq_tu_cross,
    st.b_eq_rs_cross]
  omega

/-! ## The return value -/

/-- The code's test `2bu ≤ n` is `bu ≤ cs`, since `bu + cs = n`. -/
theorem two_bu_le_n_iff_bu_le_cs :
    2 * st.b * st.u ≤ args.n ↔ st.b * st.u ≤ st.c * st.s := by
  grind only [st.bu_add_cs_eq_n]

/-- The return value, with the code's test restated: `r/s` if `bu ≤ cs`, else `t/u`. -/
public theorem rv_eq_ite_bu_le_cs :
    st.rv = if st.b * st.u ≤ st.c * st.s then st.rs else st.tu := by
  simp only [rv, st.two_bu_le_n_iff_bu_le_cs]

/-- The returned candidate is a best approximation. -/
theorem rv_best : st.rv.best := by
  grind only [st.rv_eq_ite_bu_le_cs, st.rs_best_iff, st.tu_best_iff]

end PostLoopState

namespace Arguments

variable (args : Arguments)

/-- The `limitDenominator` return value is always a best approximation. -/
public theorem limitDenominator_best : args.limitDenominator.best :=
  args.postLoopState.rv_best

end Arguments
