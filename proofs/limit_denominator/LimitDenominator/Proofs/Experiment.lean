module

/-! # Absolute value of an integer, Int.abs -/

/-- Absolute value of an integer. -/
def Int.abs (a : Int) : Int := if 0 ≤ a then a else -a

/- Basic facts about Int.abs. -/
theorem Int.abs_nonneg (a : Int) : 0 ≤ a.abs := by grind only [Int.abs]
theorem Int.abs_eq (a : Int) {b : Int} : 0 ≤ b → (a.abs = b ↔ a = b ∨ a = -b) := by
  grind only [Int.abs]
theorem Int.abs_mul (a b : Int) : (a * b).abs = a.abs * b.abs := by grind only [
  Int.abs, Int.le_total 0, Int.mul_nonneg, Int.mul_nonpos_of_nonneg_of_nonpos,
  Int.mul_nonpos_of_nonpos_of_nonneg, Int.mul_nonneg_of_nonpos_of_nonpos]

/- More support lemmas. -/
theorem Int.eq_one_or_neg_one_of_mul_eq_one {a b : Int} (hab : a * b = 1) :
    b = 1 ∨ b = -1 := by
  rw [← Int.abs_eq b (by decide)]
  exact Int.eq_one_of_mul_eq_one_left (Int.abs_nonneg b)
    (show a.abs * b.abs = 1 by grind only [Int.abs_mul a b, Int.abs])

theorem Int.pos_of_mul_pos_of_nonneg_left {a b : Int} (h1 : 0 < a * b) (h2 : 0 ≤ b) :
    0 < a := by
  exact Int.lt_of_mul_lt_mul_right (show 0 * b < a * b by grind only) h2

theorem Int.mul_nonneg_iff {a b : Int} : 0 ≤ a * b ↔ (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0) := by
  grind only [Int.le_total 0, Int.mul_nonneg, Int.mul_nonneg_of_nonpos_of_nonpos,
    Int.mul_nonpos_of_nonneg_of_nonpos, Int.mul_nonpos_of_nonpos_of_nonneg,
    Int.mul_eq_zero]

theorem Int.mul_pos_iff {a b : Int} : 0 < a * b ↔ (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by
  grind only [Int.lt_trichotomy 0, Int.mul_pos, Int.mul_pos_of_neg_of_neg,
    Int.mul_neg_of_pos_of_neg, Int.mul_neg_of_neg_of_pos]

theorem Int.divisor_le_mul {a b : Int} (h1 : 0 < a * b) : a ≤ a * b := by
  grind only [
    show 0 ≤ a * (b - 1) from
      Int.mul_nonneg_iff.mpr
      (by rcases Int.mul_pos_iff.mp h1 with ⟨a_pos, b_pos⟩ | ⟨a_neg, b_neg⟩ <;> omega)
  ]

/-! # Fraction pairs -/

/-
A fraction pair represents a potentially non-normalised fraction `num / den`, with `den`
positive. These are the main data objects in the proof.
-/

/-- A fraction, minus the lowest terms hypothesis. -/
structure FractionPair where (num : Int) (den : Int) (pos : 0 < den)

namespace FractionPair

/- In this section, let's let `ef` be a generic fraction pair. -/
variable (ef : FractionPair) {a b : Int}

/- We often just need to know that the denominator of `ef` is nonnegative or nonzero. -/
theorem nonneg : 0 ≤ ef.den := Int.le_of_lt ef.pos
theorem ne_zero : ef.den ≠ 0 := Int.ne_of_gt ef.pos

/-
The proofs below often involve either multiplying both sides of an equality or
inequality by a denominator, or the reverse operation of cancelling a denominator from
both sides. The following lemmas help with spelling those operations clearly.
-/
theorem eq_mul_den (heq : a = b) : a * ef.den = b * ef.den := by rw [heq]
theorem lt_mul_den (hlt : a < b) : a * ef.den < b * ef.den :=
  Int.mul_lt_mul_of_pos_right hlt ef.pos
theorem le_mul_den (hle : a ≤ b) : a * ef.den ≤ b * ef.den :=
  Int.mul_le_mul_of_nonneg_right hle ef.nonneg
theorem eq_of_eq_mul_den (heq : a * ef.den = b * ef.den) : a = b :=
  Int.eq_of_mul_eq_mul_right ef.ne_zero heq
theorem lt_of_lt_mul_den (hlt : a * ef.den < b * ef.den) : a < b :=
  Int.lt_of_mul_lt_mul_right hlt ef.nonneg
theorem le_of_le_mul_den (hle : a * ef.den ≤ b * ef.den) : a ≤ b :=
  Int.le_of_mul_le_mul_right hle ef.pos
theorem eq_of_eq_den {ef gh : FractionPair}
    (h_deneq : ef.den = gh.den)
    (heq : ef.num * gh.den = gh.num * ef.den)
    : ef = gh := by
  rw [FractionPair.mk.injEq]
  exact ⟨Int.eq_of_mul_eq_mul_right ef.ne_zero (h_deneq ▸ heq), h_deneq⟩

/-- A fraction pair is a half integer if it has the form k + 1/2 for some k. -/
def isHalfInteger := ∃ (k : Int), (2 * ef.num - ef.den) = 2 * ef.den * k

end FractionPair

/-! # Inputs -/

/-
The inputs to the algorithm consist of a fraction pair m/n and a positive limit on the
denominator.
-/

/-- The inputs to the algorithm: a target fraction m/n and a denominator limit. -/
structure Inputs where
  (m n limit : Int)
  n_pos : 0 < n
  limit_pos : 0 < limit

namespace Inputs

variable (args : Inputs)

abbrev mn : FractionPair := ⟨args.m, args.n, args.n_pos⟩

/-- Scaled distance from e/f to m/n. -/
def dist (ef : FractionPair) := (ef.num * args.n - args.m * ef.den).abs

/-
Given two approximations e/f and g/h to m/n, we say that e/f is *better* than g/h
if either:

- e/f is closer to m/n than g/h is, or
- e/f and g/h are equidistant from m/n, but f ≤ h.

Note the slight abuse of language: "better" suggests a non-reflexive relation, but
our "better" relation is reflexive: e/f is better than itself.
-/

/-- e/f is a better approximation to m/n than g/h is. -/
def better (ef gh : FractionPair) :=
  args.dist ef * gh.den < args.dist gh * ef.den
  ∨
  args.dist ef * gh.den = args.dist gh * ef.den ∧ ef.den ≤ gh.den

/-- The "better" relation is transitive. -/
theorem better_trans {ef gh ij : FractionPair} (h1 : args.better ef gh)
    (h2 : args.better gh ij) : args.better ef ij := by
  rcases h1 with h1 | ⟨h1, d1⟩ <;> rcases h2 with h2 | ⟨h2, d2⟩
  · left; exact gh.lt_of_lt_mul_den (by grind only [ij.lt_mul_den h1, ef.lt_mul_den h2])
  · left; exact gh.lt_of_lt_mul_den (by grind only [ij.lt_mul_den h1, ef.eq_mul_den h2])
  · left; exact gh.lt_of_lt_mul_den (by grind only [ij.eq_mul_den h1, ef.lt_mul_den h2])
  · right
    exact ⟨gh.eq_of_eq_mul_den (by grind only [ij.eq_mul_den h1, ef.eq_mul_den h2]),
      Int.le_trans d1 d2⟩

/--
A "best" approximation for the given inputs is an approximation e/f with denominator
bounded by limit which is better than any other approximation g/h with denominator
bounded by limit.
-/
def best (ef : FractionPair) :=
  ef.den ≤ args.limit ∧ ∀ {gh : FractionPair}, gh.den ≤ args.limit → args.better ef gh

/--
The ambiguous case.
-/
def ambiguous := args.limit = 1 ∧ args.mn.isHalfInteger

end Inputs

/-! # In the loop -/

structure LoopState (args : Inputs) where
  (a b p q r s v : Int)
  b_nonneg : 0 ≤ b
  b_lt_a : b < a
  q_nonneg : 0 ≤ q
  s_pos : 0 < s
  s_le_limit : s ≤ args.limit
  det : (p * s - r * q) * v = 1
  heqa : (p * args.n - args.m * q) * v = a
  heqb : (args.m * s - r * args.n) * v = b
  v_eq_one_of_q_eq_zero : q = 0 → v = 1

namespace LoopState

def initialLoopState (args : Inputs) : LoopState args where
  a := args.n
  b := args.m % args.n
  p := 1
  q := 0
  r := args.m / args.n
  s := 1
  v := 1
  det := by grind only
  b_nonneg := Int.emod_nonneg args.m (Int.ne_of_gt args.mn.pos)
  b_lt_a := Int.emod_lt_of_pos args.m args.mn.pos
  q_nonneg := by decide
  s_pos := by decide
  s_le_limit := args.limit_pos
  heqa := by grind only
  heqb := by grind only [Int.mul_ediv_add_emod args.m args.n]
  v_eq_one_of_q_eq_zero := by grind only

variable {args : Inputs} (st : LoopState args)

/-- Condition guarding iteration of the while loop. -/
def loopCondition := 0 < st.b ∧ st.q + st.a / st.b * st.s ≤ args.limit

/-- The loop condition is decidable. -/
instance : Decidable st.loopCondition := by unfold loopCondition; infer_instance

/-- The effect of one iteration of the while loop. -/
def nextLoopState (hst : st.loopCondition) : LoopState args where
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
    have k_pos : 0 < st.a / st.b :=
      (Int.le_ediv_iff_mul_le hst.1).mpr (by grind only [st.b_lt_a])
    grind only [st.q_nonneg, Int.mul_pos k_pos st.s_pos]
  s_le_limit := hst.2
  heqa := by grind only [st.heqb]
  heqb := by grind only [st.heqa, st.heqb, Int.mul_ediv_add_emod st.a st.b]
  v_eq_one_of_q_eq_zero := by grind only [st.s_pos]

/-- Starting from a given state, run the loop to completion. -/
def runLoop (st : LoopState args) : LoopState args :=
  if h : st.loopCondition then runLoop (st.nextLoopState h) else st
termination_by st.a.toNat
decreasing_by exact (Int.toNat_lt_toNat (Int.lt_of_le_of_lt st.b_nonneg st.b_lt_a)).mpr st.b_lt_a

/-- On exit of the loop, the loop condition is false. -/
theorem runLoop_loopCondition_false : ¬ st.runLoop.loopCondition := by
  fun_induction runLoop st <;> trivial

/-- Run the loop to completion starting from initial arguments. -/
def fromArgs (args : Inputs) : LoopState args :=
  runLoop (LoopState.initialLoopState args)

/-- The loop condition is false for the output of run. -/
theorem fromArgs_loopCondition_false (args : Inputs) : ¬ (fromArgs args).loopCondition :=
  runLoop_loopCondition_false (LoopState.initialLoopState args)

end LoopState

/-! # Post-loop analysis -/

/-
A `PostLoopState` is a `LoopState` whose loop condition has gone false. The state of
knowledge that gives us is the block of theorems below the structure: the loop's own r/s
and a second endpoint t/u form a Farey pair bracketing the target fraction pair m/n;
both r/s and t/u have "small" denominator (s ≤ limit and u ≤ limit), but
that s + u exceeds our denominator limit (s + u > limit), and it follows that everything
strictly between `r/s` and `t/u` has denominator exceeding `limit`. (We prove the
contrapositive of this below, as `lev_rs_or_tu_lev`: any fraction pair with denominator
no larger than `limit` must be outside the bracket, or equal to one or other of the
endpoints.)

The field `v` represents the orientation of the bracket, and from `bracket_det` it must
be either `1` or `-1`. If `v = 1` then we have

    r/s ≤ m/n < t/u

and if `v = -1` then we have

    t/u < m/n ≤ r/s

From the loop exit condition and the way that `t/u` was constructed, we further know
that in fact `m/n ≤ (r + t)/(s + u)` in case `v = 1` and `(r + t)/(s + u) ≤ m/n` in case
`v = -1`, so `m/n` is in fact bracketed by the Farey pair `r/s` and `(r + t)/(s + u)`.
`rs_lev_mn` and `mn_lev_mediant` are the two relevant statements. We derive the fact
that `m/n < t/u` (`v = 1`) or `t/u < m/n` (`v = -1`) as a consequence: `mn_lev_tu`.
-/

/-- State on exiting the loop: a loop state whose loop condition has gone false. -/
structure PostLoopState (args : Inputs) extends LoopState args where
  exited : ¬ toLoopState.loopCondition

namespace PostLoopState

/-- Convert the final loop state to the post-loop state. -/
def ofLoopState {args : Inputs} (st : LoopState args) (h : ¬ st.loopCondition) :
    PostLoopState args := ⟨st, h⟩

/- We let `st` represent the post-loop state throughout this section. -/
variable {args : Inputs} (st : PostLoopState args)

/-- The far endpoint of the bracket: `t/u` is `p/q` advanced by as many copies of `r/s`
as the denominator limit allows. -/
def t : Int := st.p + (args.limit - st.q) / st.s * st.r
def u : Int := st.q + (args.limit - st.q) / st.s * st.s

-- s ≤ l < s + q + (limit - q) / s * s, so 0 < q + (limit - q) / s * s
theorem u_pos : 0 < st.u := by
  unfold u; grind only [st.s_le_limit, Int.lt_ediv_mul (args.limit - st.q) st.s_pos]

/- The two bracket endpoints, packaged as fraction pairs. -/
abbrev rs : FractionPair := ⟨st.r, st.s, st.s_pos⟩
abbrev tu : FractionPair := ⟨st.t, st.u, st.u_pos⟩

/- Generic fraction pairs. -/
variable (ef gh ij : FractionPair)

/--
We define `st.lev` as an orientation-aware less-than-or-equal-to relation:
`st.lev ef gh` means `e/f ≤ g/h` if `st.v = 1`, and `g/h ≤ e/f` if `st.v = -1`.

`st.eqv` is defined analogously; since `v` is nonzero, it is equality of fractions
whichever way the bracket points.
-/
def eqv := ef.num * gh.den * st.v = gh.num * ef.den * st.v
def lev := ef.num * gh.den * st.v ≤ gh.num * ef.den * st.v

/-- The st.lev relation is reflexive. -/
theorem lev_refl : st.lev ef ef := Int.le_refl _

/-- The st.lev relation is transitive. -/
theorem lev_trans {ef gh ij : FractionPair}
    (h1 : st.lev ef gh) (h2 : st.lev gh ij) : st.lev ef ij :=
  gh.le_of_le_mul_den (by grind only [ij.le_mul_den h1, ef.le_mul_den h2])

/-
The facts the after-loop analysis rests on. `bracket_det` is the loop's own `det`
carried into the bracket basis; both are in scope for a post-loop state, so it cannot be
called `det` itself.
-/
theorem bracket_det : (st.t * st.s - st.r * st.u) * st.v = 1 := by
  unfold t u; grind only [st.det]

/-- v must be either 1 or -1.-/
theorem v_cases : st.v = 1 ∨ st.v = -1 := Int.eq_one_or_neg_one_of_mul_eq_one st.bracket_det

theorem u_le_limit : st.u ≤ args.limit := by
  unfold u; grind only [Int.ediv_mul_le (args.limit - st.q) (Int.ne_of_gt st.s_pos)]

theorem limit_lt_s_add_u : args.limit < st.s + st.u := by
  unfold u; grind only [Int.lt_ediv_mul (args.limit - st.q) st.s_pos]

theorem rs_lev_mn : st.lev st.rs args.mn := by
  grind only [lev, st.heqb, st.b_nonneg]

theorem mn_lev_mediant :
    args.m * (st.s + st.u) * st.v ≤ (st.r + st.t) * args.n * st.v := by
  unfold t u
  have exited := st.exited
  have : ((args.limit - st.q) / st.s + 1) * st.b ≤ st.a := by
    rcases Int.lt_or_eq_of_le st.b_nonneg with hlt | heq
    · exact (Int.le_ediv_iff_mul_le hlt).mp
        (Int.lt_iff_add_one_le.mp ((Int.ediv_lt_iff_lt_mul st.s_pos).mpr
          (by grind only [LoopState.loopCondition])))
    · grind only [st.b_lt_a, st.b_nonneg]
  rw [← st.heqa, ← st.heqb] at this; grind only

/-- m/n ≤ t/u if v = 1, and t/u ≤ m/n if v = -1. -/
theorem mn_lev_tu : st.lev args.mn st.tu :=
  Int.le_of_mul_le_mul_right
    (by grind only [
      args.mn.pos, args.mn.eq_mul_den st.bracket_det, st.tu.le_mul_den st.mn_lev_mediant])
    (Int.add_pos st.s_pos st.u_pos)

/- `st.b` is already the scaled distance from m/n to r/s -- that is what the loop
invariant `heqb` says -- so only the far endpoint needs an abbrev of its own. -/
abbrev c := (st.t * args.n - args.m * st.u) * st.v

/-- `st.rv` is the return value from limit_denominator. -/
def rv : FractionPair := if 2 * st.b * st.u ≤ args.n then st.rs else st.tu

/-- The two distances split `n` between them. -/
theorem bu_add_cs_eq_n : st.b * st.u + st.c * st.s = args.n := by
  rw [← st.heqb]; grind only [args.mn.eq_mul_den st.bracket_det]

/-- Distance for values ≤ r/s. -/
theorem dist_of_lev_rs {ef : FractionPair} (h : st.lev ef st.rs) :
    args.dist ef = (args.m * ef.den - ef.num * args.n) * st.v := by
  have rhs_nonneg : 0 ≤ (args.m * ef.den - ef.num * args.n) * st.v := by
    grind only [lev, st.v_cases, st.lev_trans h st.rs_lev_mn]
  grind only [Inputs.dist, Int.abs_eq _ rhs_nonneg, st.v_cases]

/-- Distance of r/s. -/
theorem dist_rs : args.dist st.rs = (args.m * st.s - st.r * args.n) * st.v :=
  st.dist_of_lev_rs (st.lev_refl st.rs)

/-- Distance for values ≥ t/u. -/
theorem dist_of_tu_lev {ef : FractionPair} (h : st.lev st.tu ef) :
    args.dist ef = (ef.num * args.n - args.m * ef.den) * st.v := by
  have rhs_nonneg : 0 ≤ (ef.num * args.n - args.m * ef.den) * st.v := by
    grind only [lev, st.v_cases, st.lev_trans st.mn_lev_tu h]
  grind only [Inputs.dist, Int.abs_eq _ rhs_nonneg, st.v_cases]

/-- Distance of t/u. -/
theorem dist_tu : args.dist st.tu = (st.t * args.n - args.m * st.u) * st.v :=
  st.dist_of_tu_lev (st.lev_refl st.tu)

/-- The tie break condition. -/
theorem htie (h1 : args.dist st.rs = args.dist st.tu) (h2 : st.s = st.u) : st.v = 1 := by
  rw [st.dist_rs, st.dist_tu] at h1
  unfold t u at h1
  unfold u at h2
  let k := (args.limit - st.q) / st.s
  have : st.a - st.b = k * st.b := by grind only [st.heqa, st.heqb]
  -- now 0 < a - b = kb, so both b and k are positive, so in particular 0 < k
  have := st.b_nonneg
  have := st.b_lt_a
  have : 0 < k :=
    Int.pos_of_mul_pos_of_nonneg_left (show 0 < k * st.b by omega) (by grind only)

  -- now s = q + ks
  have : st.q = (1 - k) * st.s := by grind only
  -- but s is positive and k is positive, so q = 0
  have : (1 - k) ≤ 0 := by omega
  have : (1 - k) * st.s ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (Int.le_of_lt st.s_pos)
  have := st.q_nonneg
  have q_eq_zero : st.q = 0 := by omega
  exact st.v_eq_one_of_q_eq_zero q_eq_zero

/-- If a linear combination of s and u is positive, one of the coefficients is. -/
theorem lc_pos {a b : Int} : 0 < a * st.s + b * st.u → 0 < a ∨ 0 < b := by
  intro; rcases (show 0 < a * st.s ∨ 0 < b * st.u by grind only) with h1 | h2
  · left; exact Int.pos_of_mul_pos_left h1 st.s_pos
  · right; exact Int.pos_of_mul_pos_left h2 st.u_pos

/-- A fraction pair with denominator ≤ limit must be outside the bracket. -/
theorem lev_rs_or_tu_lev {yz : FractionPair} (hyz : yz.den ≤ args.limit):
    st.lev yz st.rs ∨ st.lev st.tu yz := by
  have lc : 0 < (1 - (st.t * yz.den - yz.num * st.u) * st.v) * st.s
      + (1 - (yz.num * st.s - st.r * yz.den) * st.v) * st.u := by
    grind only [yz.eq_mul_den st.bracket_det, st.limit_lt_s_add_u]
  cases st.lc_pos lc
  · right; grind only [lev]
  · left; grind only [lev]

/-- if y/z = r/s then s ≤ z (because r/s is in lowest terms). -/
theorem den_le_of_eqv_rs {yz : FractionPair} (yz_eqv_rs : st.eqv yz st.rs) :
    st.s ≤ yz.den := by
  have : yz.den = st.s * ((st.t * yz.den - yz.num * st.u) * st.v) := by
    grind only [st.tu.eq_mul_den yz_eqv_rs, yz.eq_mul_den st.bracket_det]
  exact this ▸ Int.divisor_le_mul (this ▸ yz.pos)

/-- if y/z = t/u then u ≤ z (because t/u is in lowest terms). -/
theorem den_le_of_eqv_tu {yz : FractionPair} (yz_eqv_tu : st.eqv yz st.tu) :
    st.u ≤ yz.den := by
  have : yz.den = st.u * ((yz.num * st.s - st.r * yz.den) * st.v) := by
    grind only [st.rs.eq_mul_den yz_eqv_tu, yz.eq_mul_den st.bracket_det]
  exact this ▸ Int.divisor_le_mul (this ▸ yz.pos)

/-- r/s is at least as good as anything beyond it. -/
theorem better_rs_of_lev {yz : FractionPair} (h : st.lev yz st.rs) : args.better st.rs yz := by
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · left; rw [st.dist_rs, st.dist_of_lev_rs h]
    grind only [args.mn.lt_mul_den hlt]
  · right; refine ⟨?_, st.den_le_of_eqv_rs heq⟩; rw [st.dist_rs, st.dist_of_lev_rs h]
    grind only [args.mn.eq_mul_den heq]

/-- t/u is at least as good as anything beyond it. -/
theorem better_tu_of_lev {yz : FractionPair} (h : st.lev st.tu yz) : args.better st.tu yz := by
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · left; rw [st.dist_tu, st.dist_of_tu_lev h]
    grind only [args.mn.lt_mul_den hlt]
  · right; refine ⟨?_, st.den_le_of_eqv_tu heq.symm⟩; rw [st.dist_tu, st.dist_of_tu_lev h]
    grind only [args.mn.eq_mul_den heq]

/-- One of the two candidates is at least as good as any candidate fraction pair. -/
theorem yz_cases {yz : FractionPair} (hyz : yz.den ≤ args.limit) :
    args.better st.rs yz ∨ args.better st.tu yz :=
  (st.lev_rs_or_tu_lev hyz).imp st.better_rs_of_lev st.better_tu_of_lev

/-- The returned pair is at least as good as the other. -/
theorem rv_cases :
    st.rv = st.rs ∧ args.better st.rs st.tu ∨ st.rv = st.tu ∧ args.better st.tu st.rs := by
  have hn := args.mn.eq_mul_den st.bracket_det
  have bu_cs := st.bu_add_cs_eq_n
  rcases Int.lt_or_le (st.c * st.s) (st.b * st.u) with h1 | hrs
  · right; refine ⟨if_neg (by grind only), .inl ?_⟩
    rw [st.dist_rs, st.dist_tu, st.heqb]
    exact h1
  · rcases Int.lt_or_eq_of_le hrs with hlt | heq
    · left; refine ⟨if_pos (by grind only), .inl ?_⟩
      rw [st.dist_rs, st.dist_tu, st.heqb]
      exact hlt
    · left; refine ⟨if_pos (by grind only), .inr ⟨?_, ?_⟩⟩
      · rw [st.dist_rs, st.dist_tu, st.heqb]
        exact heq
      · have cs_pos : 0 < st.c * st.s := by
          grind only [args.mn.eq_mul_den st.bracket_det, args.mn.pos]
        have cs_le_cu : st.c * st.s ≤ st.c * st.u := by
          grind only [st.tu.le_mul_den st.mn_lev_mediant]
        exact Int.le_of_mul_le_mul_left cs_le_cu
          (Int.pos_of_mul_pos_left cs_pos st.s_pos)

/-- The returned fraction pair has denominator bounded by limit. -/
theorem rv_bounded : st.rv.den ≤ args.limit := by grind only [rv, st.s_le_limit, st.u_le_limit]

/-- The returned fraction pair is better than any candidate. -/
theorem rv_better {yz : FractionPair} (hyz : yz.den ≤ args.limit) :
    args.better st.rv yz := by
  rcases st.rv_cases with ⟨rveq, hrv⟩ | ⟨rveq, hrv⟩
    <;> rw [rveq] <;> rcases st.yz_cases hyz with h | h
  · exact h
  · exact args.better_trans hrv h
  · exact args.better_trans hrv h
  · exact h

/-- The returned fraction is a best approximation. -/
theorem rv_best : args.best st.rv := ⟨st.rv_bounded, st.rv_better⟩

/-- A best approximation beyond r/s is r/s itself. -/
theorem eq_rs_of_lev_of_best {yz : FractionPair} (h : st.lev yz st.rs) (yz_best : args.best yz) :
    yz = st.rs := by
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · -- y/z < r/s implies dist r/s < dist y/z, which contradicts yz_best
    have : args.dist st.rs * yz.den < args.dist yz * st.rs.den := by
      rw [st.dist_rs, st.dist_of_lev_rs h]
      grind only [args.mn.lt_mul_den hlt]
    grind only [Inputs.better, yz_best.2 (gh := st.rs) st.s_le_limit]
  · -- y/z = r/s and s ≤ z
    have : args.dist st.rs * yz.den = args.dist yz * st.rs.den := by
      rw [st.dist_rs, st.dist_of_lev_rs h]
      grind only [args.mn.eq_mul_den heq]
    have hle := st.den_le_of_eqv_rs heq
    rcases yz_best.2 (gh := st.rs) st.s_le_limit with h1 | ⟨h1, d1⟩ <;> try omega
    apply FractionPair.eq_of_eq_den (by grind only)
    have v_ne_zero : st.v ≠ 0 := by grind only [st.bracket_det]
    exact Int.eq_of_mul_eq_mul_right v_ne_zero heq

/-- A best approximation beyond t/u is t/u itself. -/
theorem eq_tu_of_lev_of_best {yz : FractionPair} (h : st.lev st.tu yz) (yz_best : args.best yz) :
    yz = st.tu := by
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · -- t/u < y/z implies dist t/u < dist y/z, which contradicts yz_best
    have : args.dist st.tu * yz.den < args.dist yz * st.tu.den := by
      rw [st.dist_tu, st.dist_of_tu_lev h]
      grind only [args.mn.lt_mul_den hlt]
    grind only [Inputs.better, yz_best.2 (gh := st.tu) st.u_le_limit]
  · -- t/u = y/z and u ≤ z
    have : args.dist st.tu * yz.den = args.dist yz * st.tu.den := by
      rw [st.dist_tu, st.dist_of_tu_lev h]
      grind only [args.mn.eq_mul_den heq]
    have hle := st.den_le_of_eqv_tu heq.symm
    rcases yz_best.2 (gh := st.tu) st.u_le_limit with h1 | ⟨h1, d1⟩ <;> try omega
    apply FractionPair.eq_of_eq_den (by grind only)
    have v_ne_zero : st.v ≠ 0 := by grind only [st.bracket_det]
    exact Int.eq_of_mul_eq_mul_right v_ne_zero heq.symm

/-- Any best approximation is equal to either r/s or t/u. -/
theorem eq_rs_or_eq_tu_of_best {yz : FractionPair} (yz_best : args.best yz) :
    yz = st.rs ∨ yz = st.tu :=
  (st.lev_rs_or_tu_lev yz_best.1).imp
    (st.eq_rs_of_lev_of_best · yz_best) (st.eq_tu_of_lev_of_best · yz_best)

/--
Tie case: if r/s is better than t/u and t/u is better than r/s, then limit = 1 and
m/n is a half integer.
-/
theorem rv_tie_case_pre (h1 : args.better st.rs st.tu) (h2 : args.better st.tu st.rs) :
    args.ambiguous := by
  /- The try omega eliminates 3 out of the 4 cases immediately as impossible. -/
  cases h1 <;> cases h2 <;> try omega
  /- We're left with the case where r/s and t/u are equidistant and s = u. -/
  have hbc : st.b * st.s = st.c * st.u := by grind only [st.heqb, st.dist_rs, st.dist_tu]
  have htr : (st.t - st.r) * st.v * st.s = 1 := by grind only [st.bracket_det]
  have s_eq_one : st.s = 1 := Int.eq_one_of_mul_eq_one_left (Int.le_of_lt st.s_pos) htr
  refine ⟨ by grind only [st.s_le_limit, st.u_le_limit, st.limit_lt_s_add_u], ?_ ⟩
  cases st.v_cases
  · exact ⟨st.r, by grind only [st.heqb]⟩
  · exact ⟨st.r - 1, by grind only [st.heqb]⟩

/-- If both r/s and t/u are best approximations then we're in the ambiguous case. -/
theorem rv_tie_case (h1 : args.best st.rs) (h2 : args.best st.tu) : args.ambiguous :=
  st.rv_tie_case_pre (h1.2 st.u_le_limit) (h2.2 st.s_le_limit)

/- In the ambiguous case the limit is 1, so both endpoints of the bracket have
denominator 1. -/
theorem s_eq_one_of_ambiguous (hamb : args.ambiguous) : st.s = 1 := by
  grind only [hamb.1, st.s_le_limit, st.s_pos]

theorem u_eq_one_of_ambiguous (hamb : args.ambiguous) : st.u = 1 := by
  grind only [hamb.1, st.u_le_limit, st.u_pos]

/--
Conversely, if we're in the ambiguous case then both r/s and t/u are best
approximations.
XXX Proof needs cleanup!
-/
theorem rv_tie_case_converse (hamb : args.ambiguous) : args.best st.rs ∧ args.best st.tu := by
  have s_eq_one := st.s_eq_one_of_ambiguous hamb
  have u_eq_one := st.u_eq_one_of_ambiguous hamb
  obtain ⟨lim_one, k, hk⟩ := hamb

  -- r/s and t/u are equidistant from m/n
  have : args.dist st.tu = args.dist st.rs := by
    have : 0 < args.n := args.mn.pos
    rw [dist_rs, dist_tu, s_eq_one, u_eq_one]
    have h0 : st.t * st.v = st.r * st.v + 1 := by grind only [st.bracket_det]
    have := args.mn.eq_mul_den h0
    have h1 : st.r * args.n * st.v ≤ args.m * st.s * st.v := st.rs_lev_mn
    have h2 : st.r * args.n * st.v ≤ args.m * st.v := by grind only [s_eq_one ▸ h1]
    have h3 : args.m * (st.s + st.u) * st.v ≤ (st.r + st.t) * args.n * st.v := st.mn_lev_mediant
    have h4 : 2 * args.m * st.v ≤ (st.r + st.t) * args.n * st.v := by grind only [s_eq_one ▸ h3]

    -- r * v * (2 * n) ≤ 2 * m * v
    -- so r * v ≤ 2 * m * v / (2 * n)
    have : st.r * st.v ≤ 2 * args.m * st.v / (2 * args.n) :=
      Int.le_ediv_of_mul_le (by omega) (by grind only)

    -- 2 * m * v ≤ r * v * (2 * n) + n
    -- so 2 * m * v < (r * v + 1) * (2 * n)
    have : 2 * args.m * st.v / (2 * args.n) < st.r * st.v + 1 :=
      Int.ediv_lt_of_lt_mul (by omega) (by grind only)
    have twom_div_twon : 2 * args.m * st.v / (2 * args.n) = st.r * st.v := by omega
    have twom_mod_twon : (2 * args.m * st.v) % (2 * args.n) = args.n := by
      have n_mod_twon : args.n / (2 * args.n) = 0 :=
        Int.ediv_eq_zero_of_lt args.mn.nonneg (by omega)

      rcases st.v_cases with hv | hv
      · have : 2 * args.m * st.v = 2 * args.n * k + args.n := by grind only
        rw [this, Int.mul_add_emod_self_left, Int.emod_def, n_mod_twon]
        grind only
      · have : 2 * args.m * st.v = 2 * args.n * (-1 - k) + args.n := by grind only
        rw [this, Int.mul_add_emod_self_left, Int.emod_def, n_mod_twon]
        grind only
    have : 2 * args.m * st.v = st.r * st.v * (2 * args.n) + args.n := by
      grind only [Int.ediv_mul_add_emod (2 * args.m * st.v) (2 * args.n)]

    grind only

  rcases st.rv_cases with ⟨rv_eq_rs, _⟩ | ⟨rv_eq_tu, _⟩
  · -- case where rs is returned, so rs is best
    have rs_best := rv_eq_rs ▸ st.rv_best
    refine ⟨rs_best, by grind only, fun ghlimit => args.better_trans ?_ (rs_best.2 ghlimit)⟩
    right; grind only
  · -- case where tu is returned, so tu is best
    have tu_best := rv_eq_tu ▸ st.rv_best
    refine ⟨⟨by grind only, fun ghlimit => args.better_trans ?_ (tu_best.2 ghlimit)⟩, tu_best⟩
    right; grind only

/-- If we're in the ambiguous case, then bu = cs. -/
theorem bu_eq_cs_of_ambiguous (hamb : args.ambiguous) : st.b * st.u = st.c * st.s := by
  have heqb := st.heqb
  have s_eq_one := st.s_eq_one_of_ambiguous hamb
  have u_eq_one := st.u_eq_one_of_ambiguous hamb
  obtain ⟨-, k, hk⟩ := hamb

  have v_ne_zero : st.v ≠ 0 := by grind only [st.bracket_det]
  have : 2 * st.b = (2 * (k - st.r) + 1) * st.v * args.n := by grind only
  have : (2 * (st.t - k) - 1) * st.v ≠ 0 := Int.mul_ne_zero (by omega) v_ne_zero
  have : (2 * (k - st.r) + 1) * st.v ≠ 0 := Int.mul_ne_zero (by omega) v_ne_zero
  have : 0 ≤ (2 * (st.t - k) - 1) * st.v :=
    args.mn.le_of_le_mul_den (by grind only [lev, st.mn_lev_tu])
  have : 0 ≤ (2 * (k - st.r) + 1) * st.v :=
    args.mn.le_of_le_mul_den (by grind only [lev, st.rs_lev_mn])
  have : (2 * (k - st.r) + 1) * st.v + (2 * (st.t - k) - 1) * st.v = 2 := by grind only [st.bracket_det]
  have : (2 * (k - st.r) + 1) * st.v = 1 := by omega
  have : 2 * st.b * st.u = args.n := by grind only
  have : st.b * st.u + st.c * st.s = args.n := by grind only
  grind only

/-- If we're in the ambiguous case then v = 1. -/
theorem v_eq_one_of_ambiguous (hamb : args.ambiguous) : st.v = 1 := by
  have bu_eq_cs := st.bu_eq_cs_of_ambiguous hamb
  have s_eq_u : st.s = st.u :=
    (st.s_eq_one_of_ambiguous hamb).trans (st.u_eq_one_of_ambiguous hamb).symm
  apply st.htie _ s_eq_u
  rw [st.dist_rs, st.dist_tu]
  exact st.heqb.trans
    (st.tu.eq_of_eq_mul_den (show st.b * st.u = st.c * st.u from s_eq_u ▸ bu_eq_cs))

/-- If we're in the ambiguous case then r/s = (m/n)/1 -/
theorem rs_eq_floor_of_ambiguous (hamb : args.ambiguous) : st.rs = ⟨args.m / args.n, 1, by decide⟩ := by
  have heqb := st.heqb
  have v_eq_one := st.v_eq_one_of_ambiguous hamb
  have s_eq_one := st.s_eq_one_of_ambiguous hamb
  have u_eq_one := st.u_eq_one_of_ambiguous hamb
  obtain ⟨-, k, hk : 2 * args.m - args.n = 2 * args.n * k⟩ := hamb
  have : args.m / args.n = k := (Int.ediv_eq_iff_of_pos args.mn.pos).mpr (by grind only [args.mn.pos])
  rw [FractionPair.mk.injEq]
  refine ⟨ ?_, s_eq_one ⟩
  show st.r = args.m / args.n
  have v_ne_zero : st.v ≠ 0 := by omega
  have : 2 * st.b = (2 * (k - st.r) + 1) * st.v * args.n := by grind only
  have : (2 * (st.t - k) - 1) * st.v ≠ 0 := Int.mul_ne_zero (by omega) v_ne_zero
  have : (2 * (k - st.r) + 1) * st.v ≠ 0 := Int.mul_ne_zero (by omega) v_ne_zero
  have : 0 ≤ (2 * (st.t - k) - 1) * st.v :=
    args.mn.le_of_le_mul_den (by grind only [lev, st.mn_lev_tu])
  have : 0 ≤ (2 * (k - st.r) + 1) * st.v :=
    args.mn.le_of_le_mul_den (by grind only [lev, st.rs_lev_mn])
  have : (2 * (k - st.r) + 1) * st.v + (2 * (st.t - k) - 1) * st.v = 2 := by grind only [st.bracket_det]
  grind only

/-- and t/u = ((m/n) + 1)/1 -/
theorem tu_eq_ceil_of_ambiguous (hamb : args.ambiguous) : st.tu = ⟨args.m / args.n + 1, 1, by decide⟩ := by
  have heqb := st.heqb
  have v_eq_one := st.v_eq_one_of_ambiguous hamb
  have s_eq_one := st.s_eq_one_of_ambiguous hamb
  have u_eq_one := st.u_eq_one_of_ambiguous hamb
  obtain ⟨-, k, hk : 2 * args.m - args.n = 2 * args.n * k⟩ := hamb
  have : args.m / args.n = k := (Int.ediv_eq_iff_of_pos args.mn.pos).mpr (by grind only [args.mn.pos])
  rw [FractionPair.mk.injEq]
  refine ⟨ ?_, u_eq_one ⟩
  show st.t = args.m / args.n + 1
  have v_ne_zero : st.v ≠ 0 := by omega
  have : 2 * st.b = (2 * (k - st.r) + 1) * st.v * args.n := by grind only
  have : (2 * (st.t - k) - 1) * st.v ≠ 0 := Int.mul_ne_zero (by omega) v_ne_zero
  have : (2 * (k - st.r) + 1) * st.v ≠ 0 := Int.mul_ne_zero (by omega) v_ne_zero
  have : 0 ≤ (2 * (st.t - k) - 1) * st.v :=
    args.mn.le_of_le_mul_den (by grind only [lev, st.mn_lev_tu])
  have : 0 ≤ (2 * (k - st.r) + 1) * st.v :=
    args.mn.le_of_le_mul_den (by grind only [lev, st.rs_lev_mn])
  have : (2 * (k - st.r) + 1) * st.v + (2 * (st.t - k) - 1) * st.v = 2 := by grind only [st.bracket_det]
  grind only

/-- If we're in the ambiguous case then r/s is returned. -/
theorem rv_eq_rs_of_ambiguous (hamb : args.ambiguous) : st.rv = st.rs := by
  have heqb := st.heqb
  have s_eq_one := st.s_eq_one_of_ambiguous hamb
  have u_eq_one := st.u_eq_one_of_ambiguous hamb
  obtain ⟨-, k, hk⟩ := hamb
  apply if_pos
  have v_ne_zero : st.v ≠ 0 := by grind only [st.bracket_det]
  have : 2 * st.b = (2 * (k - st.r) + 1) * st.v * args.n := by grind only
  have : (2 * (st.t - k) - 1) * st.v ≠ 0 := Int.mul_ne_zero (by omega) v_ne_zero
  have : (2 * (k - st.r) + 1) * st.v ≠ 0 := Int.mul_ne_zero (by omega) v_ne_zero
  have : 0 ≤ (2 * (st.t - k) - 1) * st.v :=
    args.mn.le_of_le_mul_den (by grind only [lev, st.mn_lev_tu])
  have : 0 ≤ (2 * (k - st.r) + 1) * st.v :=
    args.mn.le_of_le_mul_den (by grind only [lev, st.rs_lev_mn])
  have : (2 * (k - st.r) + 1) * st.v + (2 * (st.t - k) - 1) * st.v = 2 := by grind only [st.bracket_det]
  have : (2 * (k - st.r) + 1) * st.v = 1 := by omega
  have : 2 * st.b * st.u = args.n := by grind only
  grind only

/-- If we're in the ambiguous case then the return value is the floor of m/n. -/
theorem rv_eq_floor_of_ambiguous (hamb : args.ambiguous) :
    st.rv = ⟨args.m / args.n, 1, by decide⟩ := by
  rw [st.rv_eq_rs_of_ambiguous hamb, st.rs_eq_floor_of_ambiguous hamb]

end PostLoopState

namespace Inputs

variable (args : Inputs)

/-- Post loop state from inputs. -/
def postLoopState : PostLoopState args :=
  PostLoopState.ofLoopState (LoopState.fromArgs args)
    (LoopState.fromArgs_loopCondition_false args)

/-- Actual return value. -/
def rv : FractionPair := args.postLoopState.rv

/-- args.rv is a best approximation. -/
theorem rv_best : args.best args.rv := args.postLoopState.rv_best

/-
If e/f and g/h are both best approximations, then either they're
equal or we're in the ambiguous case.
-/
theorem best_unique_unless_ambiguous {ef gh : FractionPair} (hef : args.best ef) (hgh : args.best gh) :
    ef = gh ∨ args.limit = 1 ∧ args.mn.isHalfInteger := by
  let st := args.postLoopState
  rcases st.eq_rs_or_eq_tu_of_best hef with h1 | h1
  <;> rcases st.eq_rs_or_eq_tu_of_best hgh with h2 | h2
  · left; grind only
  · right; exact st.rv_tie_case (h1 ▸ hef) (h2 ▸ hgh)
  · right; exact st.rv_tie_case (h2 ▸ hgh) (h1 ▸ hef)
  · left; grind only

/--
In the ambiguous case, the only best approximations are the integers m/n and m/n + 1.
-/
theorem ambiguous_best (hamb : args.ambiguous) {yz : FractionPair} :
    let k := args.mn.num / args.mn.den
    args.best yz ↔ yz = ⟨k, 1, by decide⟩ ∨ yz = ⟨k + 1, 1, by decide⟩ := by
  intro k
  let st := args.postLoopState
  have hrs : st.rs = ⟨k, 1, by decide⟩ := st.rs_eq_floor_of_ambiguous hamb
  have htu : st.tu = ⟨k + 1, 1, by decide⟩ := st.tu_eq_ceil_of_ambiguous hamb
  obtain ⟨rs_best, tu_best⟩ := st.rv_tie_case_converse hamb
  constructor
  · intro hyz
    rcases st.eq_rs_or_eq_tu_of_best hyz with h | h
    · left; rw [h, hrs]
    · right; rw [h, htu]
  · rintro (rfl | rfl)
    · exact hrs ▸ rs_best
    · exact htu ▸ tu_best

/-- In the ambiguous case, m/n is returned. -/
theorem ambiguous_rv (hamb : args.ambiguous) :
    args.rv = ⟨args.m / args.n, 1, show 0 < 1 by decide⟩ :=
  args.postLoopState.rv_eq_floor_of_ambiguous hamb

end Inputs
