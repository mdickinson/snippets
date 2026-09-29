module

public import LimitDenominator.Proofs.Algorithm
public import LimitDenominator.Proofs.Arguments
public import LimitDenominator.Proofs.Candidate
import LimitDenominator.Proofs.BaseAnalysis
import LimitDenominator.Proofs.IntLemmas

/-!
The shipped listing's two optimizations over the simplified one, both of which trade on
the target being reduced: the fast path for a trivial input, and the loop condition's
missing `0 < b` test.
-/

/-! ## The fast path -/

/--
A set of arguments is *trivial* if the target is reduced and its denominator is already
within the limit.
-/
@[expose] public def Arguments.trivial (args : Arguments) :=
  Int.gcd args.m args.n = 1 ∧ args.n ≤ args.limit

namespace PostLoopState

/--
If `n ≤ limit` then `b = 0`. Proof: we have `bu + cs = n ≤ limit < s + u`, implying that
at least one of `b` and `c` is nonpositive. But we already know that `0 < c`.
-/
theorem b_eq_zero_of_n_le_limit {args : Arguments} (st : PostLoopState args)
    (h : args.n ≤ args.limit) : st.b = 0 := by
  have lc : (1 - st.c) * st.s + (1 - st.b) * st.u > 0 :=
    by grind only [st.bu_add_cs_eq_n, st.limit_lt_s_add_u]
  grind only [st.b_nonneg, st.c_pos, Int.pos_or_pos_of_lincomb_pos st.s_pos st.u_pos lc]

/-- If `m` and `n` are coprime and `b = 0`, then `m = r` and `n = s`. -/
theorem mn_eq_rs_of_b_eq_zero {args : Arguments} (st : PostLoopState args)
    (hmn : args.m.gcd args.n = 1) (hb : st.b = 0) :
    args.m = st.r ∧ args.n = st.s := by
  have : args.m = st.c * st.r ∧ args.n = st.c * st.s := by
    grind only [st.bt_add_cr_eq_m, st.bu_add_cs_eq_n]
  have : st.c = 1 := by
    apply Int.eq_one_of_dvd_one (Int.le_of_lt st.c_pos)
    apply Int.gcd_eq_one_iff.mp hmn st.c <;> grind only [Int.dvd_mul_right]
  grind only

end PostLoopState

/--
In the trivial case `m/n` is a best approximation to itself.

Proved by running the loop anyway: with `n ≤ limit` the residual `b` is zero on exit, so
the exit state's `r/s` is `m/n` itself, and `r/s` is best.
-/
public theorem Arguments.self_best_of_trivial (args : Arguments) (h : args.trivial) :
    Candidate.best ⟨args.m, args.n, args.n_pos, h.2⟩ := by
  let st := args.postLoopState
  have best_rs : st.rs.best := by
    rw [st.rs_best_iff]
    grind only [Int.mul_pos st.c_pos st.s_pos, st.b_eq_zero_of_n_le_limit h.2]
  grind only [st.mn_eq_rs_of_b_eq_zero h.1 (st.b_eq_zero_of_n_le_limit h.2)]

/-! ## No `0 < b` test -/

namespace LoopState

/-- If `st.b = 0` then `b` remains `0` after running the loop. -/
theorem runLoop_b_eq_zero {args : Arguments} (st : LoopState args) (hst : st.b = 0) :
    st.runLoop.b = 0 := by
  fun_induction runLoop st <;> grind only [loopCondition]

/--
For a reduced target whose denominator exceeds the limit, the residual `b` stays
positive.

Proved by running the loop on from `st`: were `b` zero it would stay zero to exit, where
`mn_eq_rs_of_b_eq_zero` puts `n = s` within the limit.
-/
public theorem b_pos {args : Arguments} (st : LoopState args)
    (hgcd : Int.gcd args.m args.n = 1) (hlim : args.limit < args.n) : 0 < st.b := by
  let pst : PostLoopState args := ⟨st.runLoop, st.runLoop_loopCondition_false⟩
  refine Int.lt_iff_le_and_ne.mpr ⟨st.b_nonneg, ?_⟩; intro
  grind only [pst.s_le_limit,
    pst.mn_eq_rs_of_b_eq_zero hgcd (by grind only [st.runLoop_b_eq_zero])]

end LoopState
