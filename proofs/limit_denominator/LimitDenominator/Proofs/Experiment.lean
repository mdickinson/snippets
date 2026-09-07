module

/-! # Absolute value of an integer -/

/-- Absolute value of an integer. -/
def Int.abs (a : Int) : Int := if 0 ≤ a then a else -a

/- Basic facts about Int.abs. -/
theorem Int.abs_nonneg (a : Int) : 0 ≤ a.abs := by grind only [Int.abs]
theorem Int.abs_eq (a : Int) {b : Int} : 0 ≤ b → (a.abs = b ↔ a = b ∨ a = -b) := by
  grind only [Int.abs]
theorem Int.abs_mul (a b : Int) : (a * b).abs = a.abs * b.abs := by grind only [
  Int.abs, Int.le_total 0, Int.mul_nonneg, Int.mul_nonpos_of_nonneg_of_nonpos,
  Int.mul_nonpos_of_nonpos_of_nonneg, Int.mul_nonneg_of_nonpos_of_nonpos]

/-! # Support lemmas for Int -/

/-- The only factors of 1 are 1 and -1. -/
theorem Int.eq_one_or_neg_one_of_mul_eq_one {a b : Int} (hab : a * b = 1) :
    b = 1 ∨ b = -1 := by
  rw [← Int.abs_eq b (by decide)]
  exact Int.eq_one_of_mul_eq_one_left (Int.abs_nonneg b)
    (show a.abs * b.abs = 1 by grind only [Int.abs_mul a b, Int.abs])

/--
If a linear combination of two positive integers is positive, then at least one of the
coefficients is positive.
-/
theorem Int.pos_or_pos_of_mul_add_mul_pos {a b c d : Int} (hc : 0 < c) (hd : 0 < d)
    (h : 0 < a * c + b * d) : 0 < a ∨ 0 < b := by
  rcases (show 0 < a * c ∨ 0 < b * d by grind only) with h1 | h2
  · left; exact Int.pos_of_mul_pos_left h1 hc
  · right; exact Int.pos_of_mul_pos_left h2 hd

/--
A product of two integers is positive iff both are positive or both are negative.
-/
theorem Int.mul_pos_iff {a b : Int} : 0 < a * b ↔ (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by
  grind only [Int.lt_trichotomy 0, Int.mul_pos, Int.mul_pos_of_neg_of_neg,
    Int.mul_neg_of_pos_of_neg, Int.mul_neg_of_neg_of_pos]

/--
A product of two integers is nonnegative iff both are nonnegative or both are nonpositive.
-/
theorem Int.mul_nonneg_iff {a b : Int} : 0 ≤ a * b ↔ (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0) := by
  grind only [Int.le_total 0, Int.mul_nonneg, Int.mul_nonneg_of_nonpos_of_nonpos,
    Int.mul_nonpos_of_nonneg_of_nonpos, Int.mul_nonpos_of_nonpos_of_nonneg,
    Int.mul_eq_zero]

/-- Any divisor of a positive product is less than or equal to the product. -/
theorem Int.divisor_le_mul {a b : Int} (h : 0 < a * b) : a ≤ a * b := by
  grind only [Int.mul_nonneg_iff (a := a) (b := b - 1), Int.mul_pos_iff.mp h]

/-! # Fraction pairs -/

/--
A *fraction pair* is a (possibly non-reduced) fraction `num / den`, with `den` positive.
-/
structure FractionPair where (num : Int) (den : Int) (pos : 0 < den)

namespace FractionPair

/- In this section, write `ef` for a generic fraction pair. -/
variable (ef : FractionPair)

/-- A fraction pair is *reduced* if its numerator and denominator are coprime. -/
def isReduced := ∃ (g h : Int), g * ef.num + h * ef.den = 1

/-- A fraction pair is a *half integer* if it has the form w + 1/2 for some integer w. -/
def isHalfInteger := ∃ (w : Int), 2 * ef.num = (2 * w + 1) * ef.den

/- We often just need to know that the denominator of `ef` is nonnegative or nonzero. -/
theorem nonneg : 0 ≤ ef.den := Int.le_of_lt ef.pos
theorem ne_zero : ef.den ≠ 0 := Int.ne_of_gt ef.pos

/-
The proofs below often involve either multiplying both sides of an equality or
inequality by a denominator, or the reverse operation of cancelling a denominator from
both sides. The following lemmas help with spelling those operations clearly.
-/
theorem eq_mul_den {a b : Int} (heq : a = b) : a * ef.den = b * ef.den := by rw [heq]
theorem lt_mul_den {a b : Int} (hlt : a < b) : a * ef.den < b * ef.den :=
  Int.mul_lt_mul_of_pos_right hlt ef.pos
theorem le_mul_den {a b : Int} (hle : a ≤ b) : a * ef.den ≤ b * ef.den :=
  Int.mul_le_mul_of_nonneg_right hle ef.nonneg
theorem eq_of_eq_mul_den {a b : Int} (heq : a * ef.den = b * ef.den) : a = b :=
  Int.eq_of_mul_eq_mul_right ef.ne_zero heq
theorem lt_of_lt_mul_den {a b : Int} (hlt : a * ef.den < b * ef.den) : a < b :=
  Int.lt_of_mul_lt_mul_right hlt ef.nonneg
theorem le_of_le_mul_den {a b : Int} (hle : a * ef.den ≤ b * ef.den) : a ≤ b :=
  Int.le_of_mul_le_mul_right hle ef.pos

/-- Two fraction pairs that are numerically equal and have equal denominator are equal. -/
theorem eq_of_eq_den {ef gh : FractionPair}
    (h_deneq : ef.den = gh.den) (heq : ef.num * gh.den = gh.num * ef.den) : ef = gh := by
  rw [FractionPair.mk.injEq]; exact ⟨ eq_of_eq_mul_den gh (h_deneq ▸ heq), h_deneq ⟩

end FractionPair

/-! # Inputs -/

/--
The inputs to the limitDenominator algorithm consist of a fraction pair m/n and a
positive limit on the denominator.
-/
structure Inputs where
  (m n limit : Int)
  n_pos : 0 < n
  limit_pos : 0 < limit

namespace Inputs

/- In this section, fix a set `args` of inputs. -/
variable (args : Inputs)

/-- Shortcut for the fraction pair m/n. -/
abbrev mn : FractionPair := ⟨args.m, args.n, args.n_pos⟩

/-- Absolute distance from e/f to m/n, scaled by both denominators. -/
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
A *best* approximation for the given inputs is an approximation `e/f` to `m/n` with
denominator `f` bounded by `limit` that is better than any other approximation `g/h`
with denominator bounded by `limit`.

We'll prove later that there's a unique best approximation to a given set of inputs,
_except_ in the *ambiguous* case where the limit is `1` and `m/n` is a half-integer.
-/
def best (ef : FractionPair) :=
  ef.den ≤ args.limit ∧ ∀ {gh : FractionPair}, gh.den ≤ args.limit → args.better ef gh

/--
We say a set of inputs is *ambiguous* if the limit is `1` and `m/n` is a half-integer.
This is the only case where we do not have a unique best approximation.
-/
def ambiguous := args.limit = 1 ∧ args.mn.isHalfInteger

end Inputs

/-! # In the loop -/

/-
The loop is the Euclidean algorithm on `m` and `n`, tracking the continued-fraction
convergents of `m/n` as it goes. `a > b ≥ 0` are the two most recent remainders. `r/s` is
the most recent convergent and `p/q` the one before it, starting from `⌊m/n⌋/1` and `1/0`,
so `q = 0` only in the initial state. Consecutive convergents lie on opposite sides of
m/n; `v ∈ {1, -1}` records which way round, with `r/s ≤ m/n < p/q` when `v = 1` and
`p/q < m/n ≤ r/s` when `v = -1`. The orientation reverses on every iteration.

The invariants tie the remainders to the convergents. `det` is the consecutive-convergent
identity `p * s - r * q = ±1`, with `v` as the sign. `heqa` and `heqb` say that `a` and `b`
are the cross-multiplied distances `|p * n - m * q|` and `|m * s - r * n|` from m/n to the
two convergents, again with `v` supplying the sign. `s_le_limit` is what the loop condition
checked before stepping to this state.
-/

/-- The loop state: the two latest Euclidean remainders, the two latest convergents, and
the orientation `v`. -/
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

variable {args : Inputs} (st : LoopState args)

/-- The state before the first iteration: remainders `n` and `m % n`, convergents `1/0`
and `⌊m/n⌋/1`. -/
def initialLoopState (args : Inputs) : LoopState args where
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
  s_le_limit := args.limit_pos
  heqa := by grind only
  heqb := by grind only [Int.mul_ediv_add_emod args.m args.n]
  v_eq_one_of_q_eq_zero := by decide

/-- Condition guarding iteration of the while loop. -/
def loopCondition := 0 < st.b ∧ st.q + st.a / st.b * st.s ≤ args.limit

/-- The state transition resulting from execution of the loop body. -/
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
    have a_ediv_b_pos : 0 < st.a / st.b :=
      (Int.le_ediv_iff_mul_le hst.1).mpr (by grind only [st.b_lt_a])
    grind only [st.q_nonneg, Int.mul_pos a_ediv_b_pos st.s_pos]
  s_le_limit := hst.2
  heqa := by grind only [st.heqb]
  heqb := by grind only [st.heqa, st.heqb, Int.mul_ediv_add_emod st.a st.b]
  v_eq_one_of_q_eq_zero := by grind only [st.s_pos]

/-- The value max(a, 0) (as a Nat) strictly decreases with each iteration of the loop. -/
theorem loop_decreases (hst : st.loopCondition) :
    (st.nextLoopState hst).a.toNat < st.a.toNat :=
  (Int.toNat_lt_toNat (Int.lt_of_le_of_lt st.b_nonneg st.b_lt_a)).mpr st.b_lt_a

/-! ## Execution of the loop -/

/-- The loop condition is decidable. -/
instance : Decidable st.loopCondition := by unfold loopCondition; infer_instance

/-- Starting from a given state, run the loop to completion. -/
def runLoop (st : LoopState args) : LoopState args :=
  if h : st.loopCondition then runLoop (st.nextLoopState h) else st
termination_by st.a.toNat
decreasing_by exact st.loop_decreases h

/-- On exit of the loop, the loop condition is false. -/
theorem runLoop_loopCondition_false : ¬ st.runLoop.loopCondition := by
  fun_induction runLoop st <;> trivial

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

/- We let `st` represent the post-loop state throughout this section. -/
variable {args : Inputs} (st : PostLoopState args)

/-! ## The bracket -/

/-- How many copies of `r/s` can be added to `p/q` without the denominator exceeding
the limit. -/
def k : Int := (args.limit - st.q) / st.s

/-- The far endpoint of the bracket: `t/u` is `p/q` advanced by `k` copies of `r/s`. -/
def t : Int := st.p + st.k * st.r
def u : Int := st.q + st.k * st.s

/-
From the definition of `k` we have `ks ≤ limit - q < (k + 1)s`,
giving `u ≤ limit < s + u`. Since also `s ≤ limit`, it follows that `0 < u`.
 -/
theorem u_le_limit : st.u ≤ args.limit := by
  grind only [k, u, Int.ediv_mul_le (args.limit - st.q) (Int.ne_of_gt st.s_pos)]
theorem limit_lt_s_add_u : args.limit < st.s + st.u := by
  grind only [k, u, Int.lt_ediv_mul (args.limit - st.q) st.s_pos]
theorem u_pos : 0 < st.u := by grind only [st.s_le_limit, st.limit_lt_s_add_u]

/- The two bracket endpoints, packaged as fraction pairs. -/
abbrev rs : FractionPair := ⟨st.r, st.s, st.s_pos⟩
abbrev tu : FractionPair := ⟨st.t, st.u, st.u_pos⟩

/-
If `0 < b`, then the loop exit condition means that we stopped short of a full Euclidean
algorithm step, so k < a/b. Proof: we have `q + ks ≤ limit` from the definition of `k`,
and `limit < q + ⌊a/b⌋s` from the loop exit condition, so `k < ⌊a/b⌋`.

In both this case and the `b = 0` case we have `(k + 1)b ≤ a`.
-/
theorem k_upper : (st.k + 1) * st.b ≤ st.a := by
  rcases Int.lt_or_eq_of_le st.b_nonneg with hlt | heq
  · exact (Int.le_ediv_iff_mul_le hlt).mp (st.rs.lt_of_lt_mul_den
      (by grind only [k, u, LoopState.loopCondition, st.exited, st.u_le_limit]))
  · grind only [st.b_lt_a, st.b_nonneg]

/-! ## Orientation-aware order -/

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

/- The `st.lev` relation is reflexive and transitive. -/
theorem lev_refl : st.lev ef ef := Int.le_refl _
theorem lev_trans {ef gh ij : FractionPair}
    (h1 : st.lev ef gh) (h2 : st.lev gh ij) : st.lev ef ij :=
  gh.le_of_le_mul_den (by grind only [ij.le_mul_den h1, ef.le_mul_den h2])

/-! ## Bracket facts -/

/-
The facts the after-loop analysis rests on. `bracket_det` is the loop's own `det`
carried into the bracket basis; both are in scope for a post-loop state, so it cannot be
called `det` itself.
-/
theorem bracket_det : (st.t * st.s - st.r * st.u) * st.v = 1 := by grind only [t, u, st.det]

/-- v must be either 1 or -1.-/
theorem v_cases : st.v = 1 ∨ st.v = -1 := Int.eq_one_or_neg_one_of_mul_eq_one st.bracket_det

/-- In particular, v is nonzero. -/
theorem v_nonzero : st.v ≠ 0 := by grind only [st.v_cases]

/- `m/n` lies between `r/s` and `(r + t)/(s + u)`, hence between `r/s` and `t/u`. -/
/-- The mediant of the two bracket endpoints. -/
def mediant : FractionPair := ⟨st.r + st.t, st.s + st.u, Int.add_pos st.s_pos st.u_pos⟩

theorem rs_lev_mn : st.lev st.rs args.mn := by grind only [lev, st.heqb, st.b_nonneg]
theorem mn_lev_mediant : st.lev args.mn st.mediant := by
  unfold lev mediant t u
  grind only [st.heqb ▸ st.heqa ▸ st.k_upper]

theorem mediant_lev_tu : st.lev st.mediant st.tu := by
  unfold mediant; grind only [lev, st.bracket_det]

/-- m/n ≤ t/u if v = 1, and t/u ≤ m/n if v = -1. -/
theorem mn_lev_tu : st.lev args.mn st.tu := st.lev_trans st.mn_lev_mediant st.mediant_lev_tu

/-! ## Distances -/

def c := st.a - st.k * st.b

/-- `c` is the scaled distance from t/u to m/n.-/
theorem heqc : st.c = (st.t * args.n - args.m * st.u) * st.v := by
  grind only [c, t, u, st.heqa, st.heqb]

/-- Since (k + 1)b ≤ a, we have b ≤ c. -/
theorem b_le_c : st.b ≤ st.c := by grind only [c, st.k_upper]

/-- The two distances split `n` between them. -/
theorem bu_add_cs_eq_n : st.b * st.u + st.c * st.s = args.n := by
  grind only [st.heqb, st.heqc, args.mn.eq_mul_den st.bracket_det]

/-- `c` is positive: one of `b` and `c` is, since `b * u + c * s = n > 0`, and `b ≤ c`. -/
theorem c_pos : 0 < st.c := by
  cases Int.pos_or_pos_of_mul_add_mul_pos st.u_pos st.s_pos (st.bu_add_cs_eq_n ▸ args.n_pos)
  <;> grind only [st.b_le_c]

/-- Distance for values ≤ r/s. -/
theorem dist_of_lev_rs {ef : FractionPair} (h : st.lev ef st.rs) :
    args.dist ef = (args.m * ef.den - ef.num * args.n) * st.v := by
  have rhs_nonneg : 0 ≤ (args.m * ef.den - ef.num * args.n) * st.v := by
    grind only [lev, st.lev_trans h st.rs_lev_mn]
  grind only [Inputs.dist, Int.abs_eq _ rhs_nonneg, st.v_cases]

/-- Distance of r/s. -/
theorem dist_rs : args.dist st.rs = (args.m * st.s - st.r * args.n) * st.v :=
  st.dist_of_lev_rs (st.lev_refl st.rs)

/-- Distance for values ≥ t/u. -/
theorem dist_of_tu_lev {ef : FractionPair} (h : st.lev st.tu ef) :
    args.dist ef = (ef.num * args.n - args.m * ef.den) * st.v := by
  have rhs_nonneg : 0 ≤ (ef.num * args.n - args.m * ef.den) * st.v := by
    grind only [lev, st.lev_trans st.mn_lev_tu h]
  grind only [Inputs.dist, Int.abs_eq _ rhs_nonneg, st.v_cases]

/-- Distance of t/u. -/
theorem dist_tu : args.dist st.tu = (st.t * args.n - args.m * st.u) * st.v :=
  st.dist_of_tu_lev (st.lev_refl st.tu)

/-! ## Bounded fractions lie outside the bracket -/

/-- A fraction pair with denominator ≤ limit must be outside the bracket. -/
theorem lev_rs_or_tu_lev {yz : FractionPair} (hyz : yz.den ≤ args.limit):
    st.lev yz st.rs ∨ st.lev st.tu yz := by
  have lc : 0 < (1 - (st.t * yz.den - yz.num * st.u) * st.v) * st.s
      + (1 - (yz.num * st.s - st.r * yz.den) * st.v) * st.u := by
    grind only [yz.eq_mul_den st.bracket_det, st.limit_lt_s_add_u]
  cases Int.pos_or_pos_of_mul_add_mul_pos st.s_pos st.u_pos lc
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
  unfold Inputs.better
  rw [st.dist_rs, st.dist_of_lev_rs h]
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · left; grind only [args.mn.lt_mul_den hlt]
  · right; exact ⟨by grind only [args.mn.eq_mul_den heq], st.den_le_of_eqv_rs heq⟩

/-- t/u is at least as good as anything beyond it. -/
theorem better_tu_of_lev {yz : FractionPair} (h : st.lev st.tu yz) : args.better st.tu yz := by
  unfold Inputs.better
  rw [st.dist_tu, st.dist_of_tu_lev h]
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · left; grind only [args.mn.lt_mul_den hlt]
  · right; exact ⟨by grind only [args.mn.eq_mul_den heq], st.den_le_of_eqv_tu heq.symm⟩

/-- One of the two candidates is at least as good as any candidate fraction pair. -/
theorem yz_cases {yz : FractionPair} (hyz : yz.den ≤ args.limit) :
    args.better st.rs yz ∨ args.better st.tu yz :=
  (st.lev_rs_or_tu_lev hyz).imp st.better_rs_of_lev st.better_tu_of_lev

/-! ## The return value -/

/-- `st.rv` is the return value from limitDenominator - either `r/s` or `t/u`. -/
def rv : FractionPair := if 2 * st.b * st.u ≤ args.n then st.rs else st.tu

/-- The returned fraction pair has denominator bounded by limit. -/
theorem rv_bounded : st.rv.den ≤ args.limit := by grind only [rv, st.s_le_limit, st.u_le_limit]

/-- Whichever bound is returned is at least as good as the other one. -/
theorem rv_cases :
    st.rv = st.rs ∧ args.better st.rs st.tu ∨ st.rv = st.tu ∧ args.better st.tu st.rs := by
  have bu_cs := st.bu_add_cs_eq_n
  rcases Int.lt_or_le (st.c * st.s) (st.b * st.u) with htu | hrs
  · right; refine ⟨if_neg (by grind only), .inl ?_⟩
    grind only [st.dist_rs, st.dist_tu, st.heqb, st.heqc]
  · rcases Int.lt_or_eq_of_le hrs with hlt | heq
    · left; refine ⟨if_pos (by grind only), .inl ?_⟩
      grind only [st.dist_rs, st.dist_tu, st.heqb, st.heqc]
    · left; refine ⟨if_pos (by grind only), .inr ⟨?_, ?_⟩⟩
      · grind only [st.dist_rs, st.dist_tu, st.heqc, args.mn.eq_mul_den st.bracket_det]
      · exact Int.le_of_mul_le_mul_left (heq ▸ st.tu.le_mul_den st.b_le_c) st.c_pos

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

/-! ## Best approximations -/

/-- A best approximation beyond r/s is r/s itself. -/
theorem eq_rs_of_lev_of_best {yz : FractionPair} (h : st.lev yz st.rs) (yz_best : args.best yz) :
    yz = st.rs := by
  have yz_rs : args.better yz st.rs := yz_best.2 st.s_le_limit
  unfold Inputs.better at yz_rs
  rw [st.dist_rs, st.dist_of_lev_rs h] at yz_rs
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · -- y/z < r/s makes r/s strictly better than y/z, contradicting yz_rs
    grind only [args.mn.lt_mul_den hlt]
  · -- y/z = r/s as fractions, so s ≤ z; yz_rs gives z ≤ s
    have ⟨_, z_le_s⟩ := Or.resolve_left yz_rs (by grind only [args.mn.eq_mul_den heq])
    exact FractionPair.eq_of_eq_den (Int.le_antisymm z_le_s (st.den_le_of_eqv_rs heq))
      (Int.eq_of_mul_eq_mul_right st.v_nonzero heq)

/-- A best approximation beyond t/u is t/u itself. -/
theorem eq_tu_of_lev_of_best {yz : FractionPair} (h : st.lev st.tu yz) (yz_best : args.best yz) :
    yz = st.tu := by
  have yz_tu : args.better yz st.tu := yz_best.2 st.u_le_limit
  unfold Inputs.better at yz_tu
  rw [st.dist_tu, st.dist_of_tu_lev h] at yz_tu
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · -- t/u < y/z makes t/u strictly better than y/z, contradicting yz_tu
    grind only [args.mn.lt_mul_den hlt]
  · -- y/z = t/u as fractions, so u ≤ z; yz_tu gives z ≤ u
    have ⟨_, z_le_u⟩ := Or.resolve_left yz_tu (by grind only [args.mn.eq_mul_den heq])
    exact FractionPair.eq_of_eq_den (Int.le_antisymm z_le_u (st.den_le_of_eqv_tu heq.symm))
      (Int.eq_of_mul_eq_mul_right st.v_nonzero heq.symm)

/-- Any best approximation is equal to either r/s or t/u. -/
theorem eq_rs_or_eq_tu_of_best {yz : FractionPair} (yz_best : args.best yz) :
    yz = st.rs ∨ yz = st.tu :=
  (st.lev_rs_or_tu_lev yz_best.1).imp
    (st.eq_rs_of_lev_of_best · yz_best) (st.eq_tu_of_lev_of_best · yz_best)

/-- If both `r/s` and `t/u` are best approximations then we're in the ambiguous case. -/
theorem ambiguous_of_rs_and_tu_best (rs_best : args.best st.rs) (tu_best : args.best st.tu) :
    args.ambiguous := by
  -- The only possible case is that r/s and t/u are equidistant from m/n and s = u.
  cases (show args.better st.rs st.tu from rs_best.2 st.u_le_limit)
  <;> cases (show args.better st.tu st.rs from tu_best.2 st.s_le_limit) <;> try omega
  have s_eq_u : st.s = st.u := by grind only
  have equidistant : args.dist st.rs * st.u = args.dist st.tu * st.s := by grind only
  rw [st.dist_rs, st.dist_tu] at equidistant
  -- From (ts - ru)v = 1 and s = u we get (t - r) v s = 1, hence s = 1
  have htr : (st.t - st.r) * st.v * st.s = 1 := by grind only [st.bracket_det]
  have s_eq_one : st.s = 1 := Int.eq_one_of_mul_eq_one_left (Int.le_of_lt st.s_pos) htr
  -- We have 0 < limit < s + u and s = u = 1, so the limit is 1.
  refine ⟨ by grind only [st.limit_lt_s_add_u, args.limit_pos], ?_ ⟩
  -- m/n is r + 1/2 if v = 1 and t + 1/2 if v = -1
  cases st.v_cases
  · exact ⟨ st.r, by grind only ⟩
  · exact ⟨ st.t, by grind only ⟩

/-! ## The ambiguous case -/

section ambiguous

/-
This section studies the special case where the input m/n is a half integer
and limit = 1.
-/

variable (hamb : args.ambiguous)
include hamb

/- In the ambiguous case both endpoints of the bracket have denominator 1. -/
theorem s_eq_one_of_ambiguous : st.s = 1 := by grind only [hamb.1, st.s_le_limit, st.s_pos]
theorem u_eq_one_of_ambiguous : st.u = 1 := by grind only [hamb.1, st.u_le_limit, st.u_pos]

/-- In the ambiguous case m/n is exactly half a unit from r/s. -/
theorem two_b_eq_n_of_ambiguous : 2 * st.b = args.n := by
  have s_eq_one := st.s_eq_one_of_ambiguous hamb
  have u_eq_one := st.u_eq_one_of_ambiguous hamb
  have heqb := st.heqb
  obtain ⟨w, hw⟩ := hamb.2
  have two_b : 2 * st.b = (2 * (w - st.r) + 1) * st.v * args.n := by grind only
  have : (2 * (st.t - w) - 1) * st.v ≠ 0 := Int.mul_ne_zero (by omega) st.v_nonzero
  have : (2 * (w - st.r) + 1) * st.v ≠ 0 := Int.mul_ne_zero (by omega) st.v_nonzero
  have : 0 ≤ (2 * (st.t - w) - 1) * st.v :=
    args.mn.le_of_le_mul_den (by grind only [lev, st.mn_lev_tu])
  have : 0 ≤ (2 * (w - st.r) + 1) * st.v :=
    args.mn.le_of_le_mul_den (by grind only [lev, st.rs_lev_mn])
  have : (2 * (w - st.r) + 1) * st.v + (2 * (st.t - w) - 1) * st.v = 2 := by
    grind only [st.bracket_det]
  have : (2 * (w - st.r) + 1) * st.v = 1 := by omega
  grind only

/-- In the ambiguous case r/s and t/u are equidistant from m/n. -/
theorem dist_rs_eq_dist_tu_of_ambiguous :
    args.dist st.rs = args.dist st.tu := by
  rw [st.dist_rs, st.dist_tu]
  grind only [st.two_b_eq_n_of_ambiguous hamb, st.bu_add_cs_eq_n, st.heqb, st.heqc,
    st.s_eq_one_of_ambiguous hamb, st.u_eq_one_of_ambiguous hamb]

/-- In the ambiguous case v = 1. -/
theorem v_eq_one_of_ambiguous : st.v = 1 := by
  -- Since s = u = q + ks, (1 - k)s = q, so k ≤ 1.
  have h1 : args.dist st.rs = args.dist st.tu := st.dist_rs_eq_dist_tu_of_ambiguous hamb
  have h2 : st.s = st.u := by
    grind only [st.s_eq_one_of_ambiguous hamb, st.u_eq_one_of_ambiguous hamb]
  have : (1 - st.k) * st.s = st.q := by grind only [u]
  have k_le_one : st.k ≤ 1 := by grind only [Int.mul_nonneg_iff.mp (this ▸ st.q_nonneg)]
  -- Given that s = u, the equidistance implies b = c.
  have : st.b = st.c := st.heqb ▸ st.heqc ▸ st.dist_rs ▸ st.dist_tu ▸ h1
  -- Since 0 < a - b and a - k * b = c = b, we have 0 < k * b, hence 0 < k
  have : 0 < st.k * st.b := by grind only [c, st.b_lt_a]
  have k_pos : 0 < st.k := by grind only [st.b_nonneg, Int.mul_pos_iff.mp this]
  -- So k = 1 and q = 0
  have : st.k = 1 := by grind only
  exact st.v_eq_one_of_q_eq_zero (by grind only)

/-- In the ambiguous case r/s = ⌊m/n⌋/1. -/
theorem rs_eq_floor_of_ambiguous :
    st.rs = ⟨args.m / args.n, 1, by decide⟩ := by
  have heqb := st.heqb
  have two_b_eq_n := st.two_b_eq_n_of_ambiguous hamb
  have v_eq_one := st.v_eq_one_of_ambiguous hamb
  have s_eq_one := st.s_eq_one_of_ambiguous hamb
  have : args.m - st.r * args.n = st.b := by grind only
  have r_eq : args.m / args.n = st.r :=
    (Int.ediv_eq_iff_of_pos args.n_pos).mpr (by grind only [args.n_pos])
  grind only

/-- In the ambiguous case t/u = (⌊m/n⌋ + 1)/1. -/
theorem tu_eq_ceil_of_ambiguous :
    st.tu = ⟨args.m / args.n + 1, 1, by decide⟩ := by
  have r_eq_floor : st.r = args.m / args.n :=
    congrArg FractionPair.num (st.rs_eq_floor_of_ambiguous hamb)
  have v_eq_one := st.v_eq_one_of_ambiguous hamb
  have s_eq_one := st.s_eq_one_of_ambiguous hamb
  have u_eq_one := st.u_eq_one_of_ambiguous hamb
  grind only [st.bracket_det]

/-- In the ambiguous case r/s is returned. -/
theorem rv_eq_rs_of_ambiguous : st.rv = st.rs :=
  if_pos (by grind only [st.two_b_eq_n_of_ambiguous hamb, st.u_eq_one_of_ambiguous hamb])

/-- In the ambiguous case, both endpoints are best approximations. -/
theorem best_rs_and_best_tu_of_ambiguous :
    args.best st.rs ∧ args.best st.tu := by
  have tie := st.dist_rs_eq_dist_tu_of_ambiguous hamb
  have s_eq_one := st.s_eq_one_of_ambiguous hamb
  have u_eq_one := st.u_eq_one_of_ambiguous hamb
  have tu_rs : args.better st.tu st.rs := .inr ⟨by grind only, by grind only⟩
  have rs_best := st.rv_eq_rs_of_ambiguous hamb ▸ st.rv_best
  exact ⟨rs_best, st.u_le_limit, fun h => args.better_trans tu_rs (rs_best.2 h)⟩

/-- In the ambiguous case ⌊m/n⌋ is returned. -/
theorem rv_eq_floor_of_ambiguous :
    st.rv = ⟨args.m / args.n, 1, by decide⟩ := by
  rw [st.rv_eq_rs_of_ambiguous hamb, st.rs_eq_floor_of_ambiguous hamb]

end ambiguous

end PostLoopState

namespace Inputs

variable (args : Inputs)

/-- The state on exit from the loop, run from the initial state. -/
def postLoopState : PostLoopState args :=
  let loopState := LoopState.initialLoopState args
  ⟨loopState.runLoop, loopState.runLoop_loopCondition_false⟩

/-- The full algorithm, end to end. -/
def limitDenominator : FractionPair := args.postLoopState.rv

/-! # Results -/

/-! ## Existence and uniqueness of best approximations -/

/-- In the non-ambiguous case, there's a unique best approximation. -/
theorem non_ambiguous_best (not_amb : ¬ args.ambiguous) {ef gh : FractionPair}
    (hef : args.best ef) (hgh : args.best gh) : ef = gh := by
  let st := args.postLoopState
  cases st.eq_rs_or_eq_tu_of_best hef <;> cases st.eq_rs_or_eq_tu_of_best hgh
  <;> grind only [st.ambiguous_of_rs_and_tu_best]

/-- In the ambiguous case, the best approximations are exactly ⌊m/n⌋ and ⌊m/n⌋ + 1. -/
theorem ambiguous_best (hamb : args.ambiguous) {yz : FractionPair} :
    args.best yz ↔
      yz = ⟨args.m / args.n, 1, by decide⟩ ∨ yz = ⟨args.m / args.n + 1, 1, by decide⟩ := by
  let st := args.postLoopState
  have hrs := st.rs_eq_floor_of_ambiguous hamb
  have htu := st.tu_eq_ceil_of_ambiguous hamb
  obtain ⟨rs_best, tu_best⟩ := st.best_rs_and_best_tu_of_ambiguous hamb
  constructor
  · intro hyz
    rcases st.eq_rs_or_eq_tu_of_best hyz with h | h
    · left; rw [h, hrs]
    · right; rw [h, htu]
  · rintro (rfl | rfl)
    · exact hrs ▸ rs_best
    · exact htu ▸ tu_best

/-! ## Any best approximation is reduced -/

/-- A best approximation is one of the two bracket endpoints, and both are in lowest
terms, with Bézout coefficients read off `bracket_det`. -/
theorem isReduced_of_best {ef : FractionPair} (hef : args.best ef) : ef.isReduced := by
  let st := args.postLoopState
  rcases st.eq_rs_or_eq_tu_of_best hef with rfl | rfl
  · exact ⟨-st.u * st.v, st.t * st.v, by grind only [st.bracket_det]⟩
  · exact ⟨st.s * st.v, -st.r * st.v, by grind only [st.bracket_det]⟩

/-! ## The return value -/

/-- The limitDenominator return value is always a best approximation. -/
theorem limitDenominator_best : args.best args.limitDenominator := args.postLoopState.rv_best

/-- In the ambiguous case, ⌊m/n⌋ is returned. -/
theorem limitDenominator_ambiguous_case (hamb : args.ambiguous) :
    args.limitDenominator = ⟨args.m / args.n, 1, by decide⟩ :=
  args.postLoopState.rv_eq_floor_of_ambiguous hamb

end Inputs
