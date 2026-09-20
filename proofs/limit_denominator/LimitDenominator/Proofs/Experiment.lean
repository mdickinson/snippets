module

public import LimitDenominator.Definitions.Specification
public import LimitDenominator.Proofs.SupportLemmas

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
theorem Int.pos_or_pos_of_mul_add_mul_pos {a b c d : Int}
    (c_pos : 0 < c) (d_pos : 0 < d) (lc_pos : 0 < a * c + b * d) : 0 < a ∨ 0 < b := by
  rcases (show 0 < a * c ∨ 0 < b * d by omega) with h1 | h2
  · left; exact Int.pos_of_mul_pos_left h1 c_pos
  · right; exact Int.pos_of_mul_pos_left h2 d_pos

/--
A product of two integers is positive iff both are positive or both are negative.
-/
theorem Int.mul_pos_iff {a b : Int} :
    0 < a * b ↔ (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by
  grind only [Int.lt_trichotomy 0, Int.mul_pos, Int.mul_pos_of_neg_of_neg,
    Int.mul_neg_of_pos_of_neg, Int.mul_neg_of_neg_of_pos]

/--
A product of two integers is nonnegative iff both are nonnegative or both are
nonpositive.
-/
theorem Int.mul_nonneg_iff {a b : Int} :
    0 ≤ a * b ↔ (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0) := by
  grind only [Int.le_total 0, Int.mul_nonneg, Int.mul_nonneg_of_nonpos_of_nonpos,
    Int.mul_nonpos_of_nonneg_of_nonpos, Int.mul_nonpos_of_nonpos_of_nonneg,
    Int.mul_eq_zero]

/-- Any divisor of a positive product is less than or equal to the product. -/
theorem Int.divisor_le_mul {a b : Int} (h : 0 < a * b) : a ≤ a * b := by
  grind only [Int.mul_nonneg_iff (a := a) (b := b - 1), Int.mul_pos_iff.mp h]

/-! # Multiplying and cancelling a positive factor -/

/-
The proofs below often multiply both sides of an equality or inequality by a positive
integer, or cancel that factor again. All six lemmas take the factor's positivity
first, so that call sites read alike.

`eq_mul_pos` has no use for `_hc`; it takes it only for that uniformity.
-/
theorem Int.eq_mul_pos {a b c : Int} (_hc : 0 < c) (heq : a = b) : a * c = b * c := by
  rw [heq]
theorem Int.lt_mul_pos {a b c : Int} (hc : 0 < c) (hlt : a < b) : a * c < b * c :=
  Int.mul_lt_mul_of_pos_right hlt hc
theorem Int.le_mul_pos {a b c : Int} (hc : 0 < c) (hle : a ≤ b) : a * c ≤ b * c :=
  Int.mul_le_mul_of_nonneg_right hle (Int.le_of_lt hc)
theorem Int.eq_of_eq_mul_pos {a b c : Int} (hc : 0 < c) (heq : a * c = b * c) : a = b :=
  Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hc) heq
theorem Int.lt_of_lt_mul_pos {a b c : Int} (hc : 0 < c) (hlt : a * c < b * c) : a < b :=
  Int.lt_of_mul_lt_mul_right hlt (Int.le_of_lt hc)
theorem Int.le_of_le_mul_pos {a b c : Int} (hc : 0 < c) (hle : a * c ≤ b * c) : a ≤ b :=
  Int.le_of_mul_le_mul_right hle hc

/-! # Arguments -/

/--
The arguments to the limitDenominator algorithm consist of a fraction `m/n` with `n`
positive, and a positive limit on the denominator.
-/
public structure Arguments where
  /-- Numerator of the fraction to be approximated. -/
  m : Int
  /-- Denominator of the fraction to be approximated. -/
  n : Int
  /-- Upper bound on the denominator of the approximation. -/
  limit : Int
  n_pos : 0 < n
  one_le_limit : 1 ≤ limit

namespace Arguments

/- In this section, fix arguments `args`. -/
variable (args : Arguments)

/--
A *candidate* solution to the problem is a (possibly non-reduced) fraction `num / den`
whose denominator is positive and bounded by the given limit. We're interested in
finding the candidate that offers the best approximation to `m/n`, in a sense to be
made precise below.
-/
public structure Candidate where
  /-- Numerator of the candidate fraction. -/
  num : Int
  /-- Denominator of the candidate fraction. -/
  den : Int
  pos : 0 < den
  den_limited : den ≤ args.limit

/-- A candidate is *reduced* if its numerator and denominator are coprime. -/
def Candidate.isReduced {args : Arguments} (ef : args.Candidate) :=
  ∃ (g h : Int), g * ef.num + h * ef.den = 1

/--
Two candidates that are numerically equal and have equal denominator are equal.
-/
theorem Candidate.eq_of_eq_den {args : Arguments} {ef gh : args.Candidate}
    (h_deneq : ef.den = gh.den) (heq : ef.num * gh.den = gh.num * ef.den) :
    ef = gh := by
  rw [Candidate.mk.injEq]
  exact ⟨ Int.eq_of_eq_mul_pos gh.pos (h_deneq ▸ heq), h_deneq ⟩

/-
Now to define what *best* means for a candidate.

Given candidates e/f and g/h, we say that e/f is *better* than g/h
if either:

- e/f is closer to m/n than g/h is, or
- e/f and g/h are equidistant from m/n, but f ≤ h.

Note the slight abuse of language: "better" suggests a non-reflexive relation, but
our "better" relation is reflexive: e/f is better than itself.

A *best* candidate is then a candidate that's better than any other candidate.
-/

/-- Absolute distance from m/n to e/f, scaled by both denominators. -/
def dist (ef : args.Candidate) := (ef.num * args.n - args.m * ef.den).abs

/-- Definition of the *better* relation. -/
def better (ef gh : args.Candidate) :=
  args.dist ef * gh.den < args.dist gh * ef.den
  ∨
  args.dist ef * gh.den = args.dist gh * ef.den ∧ ef.den ≤ gh.den

/-- The `better` relation is reflexive. -/
theorem better_refl (ef : args.Candidate) : args.better ef ef := by
  right; exact ⟨rfl, Int.le_rfl⟩

/-- The `better` relation is transitive. -/
theorem better_trans {ef gh ij : args.Candidate} (h1 : args.better ef gh)
    (h2 : args.better gh ij) : args.better ef ij := by
  rcases h1 with h1 | ⟨h1, d1⟩ <;> rcases h2 with h2 | ⟨h2, d2⟩
  · left; exact Int.lt_of_lt_mul_pos gh.pos
      (by grind only [Int.lt_mul_pos ij.pos h1, Int.lt_mul_pos ef.pos h2])
  · left; exact Int.lt_of_lt_mul_pos gh.pos
      (by grind only [Int.lt_mul_pos ij.pos h1, Int.eq_mul_pos ef.pos h2])
  · left; exact Int.lt_of_lt_mul_pos gh.pos
      (by grind only [Int.eq_mul_pos ij.pos h1, Int.lt_mul_pos ef.pos h2])
  · right
    exact ⟨Int.eq_of_eq_mul_pos gh.pos
        (by grind only [Int.eq_mul_pos ij.pos h1, Int.eq_mul_pos ef.pos h2]),
      Int.le_trans d1 d2⟩

/-- The `better` relation is total. -/
theorem better_total (ef gh : args.Candidate) :
    args.better ef gh ∨ args.better gh ef := by
  rcases Int.lt_trichotomy (args.dist ef * gh.den) (args.dist gh * ef.den)
    with (hdist | hdist | hdist)
  · left; left; exact hdist
  · rcases Int.le_total ef.den gh.den with (hden | hden)
    · left; right; exact ⟨ hdist, hden ⟩
    · right; right; exact ⟨ hdist.symm, hden ⟩
  · right; left; exact hdist

/-- Definition of *best*. -/
public def best (ef : args.Candidate) := ∀ (gh : args.Candidate), args.better ef gh

/--
We say a set of arguments is *ambiguous* if the limit is `1` and `m/n` is a
half-integer, that is, `m/n = w + 1/2` for some integer `w`. This is the only case
where we do not have a unique best approximation.
-/
public def ambiguous := args.limit = 1 ∧ ∃ (w : Int), 2 * args.m = (2 * w + 1) * args.n

/-- `⌊m/n⌋`, as a candidate. It and `floorAddOne` turn out to be exactly the best
approximations in the ambiguous case. -/
@[expose] public def floor : args.Candidate :=
  ⟨args.m / args.n, 1, by decide, args.one_le_limit⟩
def floorAddOne : args.Candidate :=
  ⟨args.m / args.n + 1, 1, by decide, args.one_le_limit⟩

end Arguments

/-! # In the loop -/

/-
The loop is the Euclidean algorithm on `m` and `n`, tracking the continued-fraction
convergents of `m/n` as it goes. `a > b ≥ 0` are the two most recent remainders. `r/s`
is the most recent convergent and `p/q` the one before it, starting from `⌊m/n⌋/1` and
`1/0`, so `q = 0` only in the initial state. Consecutive convergents lie on opposite
sides of m/n; `v ∈ {1, -1}` records which way round, with `r/s ≤ m/n < p/q` when `v = 1`
and `p/q < m/n ≤ r/s` when `v = -1`. The orientation reverses on every iteration.

The invariants tie the remainders to the convergents. `det` is the
consecutive-convergent identity `p * s - r * q = ±1`, with `v` as the sign.
`a_eq_pq_cross` and `b_eq_rs_cross` say that `a` and `b` are the cross-multiplied
distances `|p * n - m * q|` and `|m * s - r * n|` from m/n to the two convergents, again
with `v` supplying the sign. `s_le_limit` is what the loop condition checked before
stepping to this state.
-/

/-- The loop state: the two latest Euclidean remainders, the two latest convergents, and
the orientation `v`. -/
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
  /-- The orientation: `1` where `r/s ≤ m/n`, `-1` where `m/n ≤ r/s`. -/
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

/-- The state before the first iteration: remainders `n` and `m % n`, convergents `1/0`
and `⌊m/n⌋/1`. -/
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

/--
The value max(a, 0) (as a Nat) strictly decreases with each iteration of the loop.
-/
theorem loop_decreases (hst : st.loopCondition) :
    (st.nextLoopState hst).a.toNat < st.a.toNat :=
  (Int.toNat_lt_toNat (Int.lt_of_le_of_lt st.b_nonneg st.b_lt_a)).mpr st.b_lt_a

/-! ## Execution of the loop -/

/-- The loop condition is decidable. -/
public instance : Decidable st.loopCondition := by unfold loopCondition; infer_instance

/-- Starting from a given state, run the loop to completion. -/
@[expose] public def runLoop (st : LoopState args) : LoopState args :=
  if h : st.loopCondition then runLoop (st.nextLoopState h) else st
termination_by st.a.toNat
decreasing_by exact st.loop_decreases h

/-- On exit of the loop, the loop condition is false. -/
public theorem runLoop_loopCondition_false : ¬ st.runLoop.loopCondition := by
  fun_induction runLoop st <;> trivial

end LoopState

/-! # Post-loop analysis -/

/-
A `PostLoopState` is a `LoopState` whose loop condition has gone false. The state of
knowledge that gives us is the block of theorems below the structure: the loop's own r/s
and a second endpoint t/u form a Farey pair bracketing the target fraction m/n;
both r/s and t/u have "small" denominator (s ≤ limit and u ≤ limit), but
that s + u exceeds our denominator limit (s + u > limit), and it follows that everything
strictly between `r/s` and `t/u` has denominator exceeding `limit`. (We prove the
contrapositive of this below, as `lev_rs_or_tu_lev`: every candidate must be outside
the bracket, or equal to one or other of the endpoints.)

The field `v` represents the orientation of the bracket, and from `bracket_det` it must
be either `1` or `-1`. If `v = 1` then we have

    r/s ≤ m/n < t/u

and if `v = -1` then we have

    t/u < m/n ≤ r/s

`rs_lev_mn` and `mn_lev_tu` state this, in the non-strict form the later proofs use.
-/

/-- State on exiting the loop: a loop state whose loop condition has gone false. -/
public structure PostLoopState (args : Arguments) extends LoopState args where
  exited : ¬ toLoopState.loopCondition

namespace PostLoopState

/- We let `st` represent the post-loop state throughout this section. -/
variable {args : Arguments} (st : PostLoopState args)

/-! ## The bracket -/

/--
The number of copies of `r/s` that can be "added" to `p/q` without the denominator
exceeding the limit.
-/
@[expose] public def k : Int := (args.limit - st.q) / st.s

/-- Numerator of the far endpoint of the bracket: `t/u` is `p/q` advanced by `k`
copies of `r/s`. -/
@[expose] public def t : Int := st.p + st.k * st.r
/-- Denominator of that same far endpoint. -/
@[expose] public def u : Int := st.q + st.k * st.s

/-
From the definition of `k` we have `ks ≤ limit - q < (k + 1)s`,
giving `u ≤ limit < s + u`. Since also `s ≤ limit`, it follows that `0 < u`.
 -/
public theorem u_le_limit : st.u ≤ args.limit := by
  grind only [k, u, Int.ediv_mul_le (args.limit - st.q) (Int.ne_of_gt st.s_pos)]
theorem limit_lt_s_add_u : args.limit < st.s + st.u := by
  grind only [k, u, Int.lt_ediv_mul (args.limit - st.q) st.s_pos]
public theorem u_pos : 0 < st.u := by grind only [st.s_le_limit, st.limit_lt_s_add_u]

/-- The near bracket endpoint `r/s`, packaged as a candidate. -/
public abbrev rs : args.Candidate := ⟨st.r, st.s, st.s_pos, st.s_le_limit⟩
/-- The far bracket endpoint `t/u`, packaged as a candidate. -/
public abbrev tu : args.Candidate := ⟨st.t, st.u, st.u_pos, st.u_le_limit⟩

/-
If `0 < b`, then the loop exit condition means that we stopped short of a full Euclidean
algorithm step, so k < a/b. Proof: we have `q + ks ≤ limit` from the definition of `k`,
and `limit < q + ⌊a/b⌋s` from the loop exit condition, so `k < ⌊a/b⌋`.

In both this case and the `b = 0` case we have `(k + 1)b ≤ a`.
-/
theorem k_upper : (st.k + 1) * st.b ≤ st.a := by
  rcases Int.lt_or_eq_of_le st.b_nonneg with hlt | heq
  · exact (Int.le_ediv_iff_mul_le hlt).mp (Int.lt_of_lt_mul_pos st.s_pos
      (by grind only [k, u, LoopState.loopCondition, st.exited, st.u_le_limit]))
  · grind only [st.b_lt_a, st.b_nonneg]

/-! ## Orientation-aware order -/

/- Generic candidates. -/
variable (ef gh : args.Candidate)

/--
We define `st.lev` as an orientation-aware less-than-or-equal-to relation:
`st.lev ef gh` means `e/f ≤ g/h` if `st.v = 1`, and `g/h ≤ e/f` if `st.v = -1`.

`st.eqv` is defined analogously; since `v` is nonzero, it is equality of fractions
whichever way the bracket points.
-/
def eqv := ef.num * gh.den * st.v = gh.num * ef.den * st.v
def lev := ef.num * gh.den * st.v ≤ gh.num * ef.den * st.v

/-! ## Bracket facts -/

/-
The facts the after-loop analysis rests on. `bracket_det` is the loop's own `det`
carried into the bracket basis; both are in scope for a post-loop state, so it cannot be
called `det` itself.
-/
theorem bracket_det : (st.t * st.s - st.r * st.u) * st.v = 1 := by
  grind only [t, u, st.det]

/-- v must be either 1 or -1. -/
theorem v_cases : st.v = 1 ∨ st.v = -1 :=
  Int.eq_one_or_neg_one_of_mul_eq_one st.bracket_det

/-- In particular, v is nonzero. -/
theorem v_nonzero : st.v ≠ 0 := by grind only [st.v_cases]

/-- The near endpoint `r/s` is in lowest terms, with Bézout coefficients read off
`bracket_det`. -/
theorem isReduced_rs : st.rs.isReduced :=
  ⟨-st.u * st.v, st.t * st.v, by grind only [st.bracket_det]⟩

/-- The far endpoint `t/u` likewise, from the same determinant. -/
theorem isReduced_tu : st.tu.isReduced :=
  ⟨st.s * st.v, -st.r * st.v, by grind only [st.bracket_det]⟩

/-! ## Distances -/

/--
`a` reduced by `k` copies of `b`. Where `b` measures `m/n` from `r/s`, `c` measures
`t/u` from `m/n`.
-/
def c := st.a - st.k * st.b

/-- Since (k + 1)b ≤ a, we have b ≤ c. -/
theorem b_le_c : st.b ≤ st.c := by grind only [c, st.k_upper]

/-- `c` is positive: follows from `0 ≤ b ≤ c`, `b < a` and the definition of `c`. -/
theorem c_pos : 0 < st.c := by grind only [st.b_nonneg, c, st.b_le_c, st.b_lt_a]

/-- `c` is the cross-multiplied distance from `m/n` to `t/u`, oriented by `v`. -/
theorem c_eq_tu_cross : (st.t * args.n - args.m * st.u) * st.v = st.c := by
  grind only [c, t, u, st.a_eq_pq_cross, st.b_eq_rs_cross]

/- These two place `m/n` between the endpoints: `r/s ≤ m/n ≤ t/u` when `v = 1`, and
`t/u ≤ m/n ≤ r/s` when `v = -1`. -/
theorem rs_lev_mn : st.r * args.n * st.v ≤ args.m * st.s * st.v := by
  grind only [st.b_eq_rs_cross, st.b_nonneg]
theorem mn_lev_tu : args.m * st.u * st.v ≤ st.t * args.n * st.v := by
  grind only [st.c_eq_tu_cross, st.c_pos]

/-- The two distances split `n` between them. -/
theorem bu_add_cs_eq_n : st.b * st.u + st.c * st.s = args.n := by
  grind only [st.b_eq_rs_cross, st.c_eq_tu_cross,
    Int.eq_mul_pos args.n_pos st.bracket_det]

/-- Distance for values ≤ r/s. -/
theorem dist_of_lev_rs {ef : args.Candidate} (h : st.lev ef st.rs) :
    args.dist ef = (args.m * ef.den - ef.num * args.n) * st.v := by
  have rhs_nonneg : 0 ≤ (args.m * ef.den - ef.num * args.n) * st.v :=
    Int.le_of_le_mul_pos st.s_pos (by grind only [
      Int.le_mul_pos args.n_pos h, Int.le_mul_pos ef.pos st.rs_lev_mn])
  grind only [Arguments.dist, Int.abs_eq _ rhs_nonneg, st.v_cases]

/-- Distance of r/s. -/
theorem dist_rs : args.dist st.rs = (args.m * st.s - st.r * args.n) * st.v :=
  st.dist_of_lev_rs Int.le_rfl

/-- Distance for values ≥ t/u. -/
theorem dist_of_tu_lev {ef : args.Candidate} (h : st.lev st.tu ef) :
    args.dist ef = (ef.num * args.n - args.m * ef.den) * st.v := by
  have rhs_nonneg : 0 ≤ (ef.num * args.n - args.m * ef.den) * st.v :=
    Int.le_of_le_mul_pos st.u_pos (by grind only [
      Int.le_mul_pos ef.pos st.mn_lev_tu, Int.le_mul_pos args.n_pos h])
  grind only [Arguments.dist, Int.abs_eq _ rhs_nonneg, st.v_cases]

/-- Distance of t/u. -/
theorem dist_tu : args.dist st.tu = (st.t * args.n - args.m * st.u) * st.v :=
  st.dist_of_tu_lev Int.le_rfl

/-! ## Bounded fractions lie outside the bracket -/

/-- A candidate lies outside the bracket, or at one of its endpoints. -/
theorem lev_rs_or_tu_lev (yz : args.Candidate) :
    st.lev yz st.rs ∨ st.lev st.tu yz := by
  have lc : 0 < (1 - (st.t * yz.den - yz.num * st.u) * st.v) * st.s
      + (1 - (yz.num * st.s - st.r * yz.den) * st.v) * st.u := by
    grind only [
      Int.eq_mul_pos yz.pos st.bracket_det, st.limit_lt_s_add_u, yz.den_limited]
  cases Int.pos_or_pos_of_mul_add_mul_pos st.s_pos st.u_pos lc
  · right; grind only [lev]
  · left; grind only [lev]

/-- if y/z = r/s then s ≤ z (because r/s is in lowest terms). -/
theorem den_le_of_eqv_rs {yz : args.Candidate} (yz_eqv_rs : st.eqv yz st.rs) :
    st.s ≤ yz.den := by
  have : yz.den = st.s * ((st.t * yz.den - yz.num * st.u) * st.v) := by
    grind only [Int.eq_mul_pos st.u_pos yz_eqv_rs, Int.eq_mul_pos yz.pos st.bracket_det]
  exact this ▸ Int.divisor_le_mul (this ▸ yz.pos)

/-- if y/z = t/u then u ≤ z (because t/u is in lowest terms). -/
theorem den_le_of_tu_eqv {yz : args.Candidate} (tu_eqv_yz : st.eqv st.tu yz) :
    st.u ≤ yz.den := by
  have : yz.den = st.u * ((yz.num * st.s - st.r * yz.den) * st.v) := by
    grind only [Int.eq_mul_pos st.s_pos tu_eqv_yz, Int.eq_mul_pos yz.pos st.bracket_det]
  exact this ▸ Int.divisor_le_mul (this ▸ yz.pos)

/-- r/s is at least as good as anything beyond it. -/
theorem better_rs_of_lev {yz : args.Candidate} (h : st.lev yz st.rs) :
    args.better st.rs yz := by
  unfold Arguments.better
  rw [st.dist_rs, st.dist_of_lev_rs h]
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · left; grind only [Int.lt_mul_pos args.n_pos hlt]
  · right
    exact ⟨by grind only [Int.eq_mul_pos args.n_pos heq], st.den_le_of_eqv_rs heq⟩

/-- t/u is at least as good as anything beyond it. -/
theorem better_tu_of_lev {yz : args.Candidate} (h : st.lev st.tu yz) :
    args.better st.tu yz := by
  unfold Arguments.better
  rw [st.dist_tu, st.dist_of_tu_lev h]
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · left; grind only [Int.lt_mul_pos args.n_pos hlt]
  · right
    exact ⟨by grind only [Int.eq_mul_pos args.n_pos heq], st.den_le_of_tu_eqv heq⟩

/-- One of the two endpoints is at least as good as any candidate. -/
theorem better_rs_or_better_tu (yz : args.Candidate) :
    args.better st.rs yz ∨ args.better st.tu yz :=
  (st.lev_rs_or_tu_lev yz).imp st.better_rs_of_lev st.better_tu_of_lev

/-! ## Best approximations -/

variable {yz : args.Candidate}

/-- A best approximation beyond r/s is r/s itself. -/
theorem eq_rs_of_lev_of_best (h : st.lev yz st.rs) (yz_best : args.best yz) :
    yz = st.rs := by
  have yz_rs : args.better yz st.rs := yz_best st.rs
  unfold Arguments.better at yz_rs
  rw [st.dist_rs, st.dist_of_lev_rs h] at yz_rs
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · -- y/z < r/s makes r/s strictly better than y/z, contradicting yz_rs
    grind only [Int.lt_mul_pos args.n_pos hlt]
  · -- y/z = r/s as fractions, so s ≤ z; yz_rs gives z ≤ s
    have ⟨_, z_le_s⟩ :=
      Or.resolve_left yz_rs (by grind only [Int.eq_mul_pos args.n_pos heq])
    exact Arguments.Candidate.eq_of_eq_den
      (Int.le_antisymm z_le_s (st.den_le_of_eqv_rs heq))
      (Int.eq_of_mul_eq_mul_right st.v_nonzero heq)

/-- A best approximation beyond t/u is t/u itself. -/
theorem eq_tu_of_lev_of_best (h : st.lev st.tu yz) (yz_best : args.best yz) :
    yz = st.tu := by
  have yz_tu : args.better yz st.tu := yz_best st.tu
  unfold Arguments.better at yz_tu
  rw [st.dist_tu, st.dist_of_tu_lev h] at yz_tu
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · -- t/u < y/z makes t/u strictly better than y/z, contradicting yz_tu
    grind only [Int.lt_mul_pos args.n_pos hlt]
  · -- y/z = t/u as fractions, so u ≤ z; yz_tu gives z ≤ u
    have ⟨_, z_le_u⟩ :=
      Or.resolve_left yz_tu (by grind only [Int.eq_mul_pos args.n_pos heq])
    exact Arguments.Candidate.eq_of_eq_den
      (Int.le_antisymm z_le_u (st.den_le_of_tu_eqv heq))
      (Int.eq_of_mul_eq_mul_right st.v_nonzero heq.symm)

/-- Any best approximation is equal to either r/s or t/u. -/
theorem eq_rs_or_eq_tu_of_best (yz_best : args.best yz) :
    yz = st.rs ∨ yz = st.tu :=
  (st.lev_rs_or_tu_lev yz).imp (st.eq_rs_of_lev_of_best · yz_best)
    (st.eq_tu_of_lev_of_best · yz_best)

/-- At least one of r/s and t/u _is_ a best approximation. -/
theorem rs_best_or_tu_best : args.best st.rs ∨ args.best st.tu :=
  (args.better_total st.rs st.tu).imp
    (fun rs_tu gh => (st.better_rs_or_better_tu gh).elim id (args.better_trans rs_tu))
    (fun tu_rs gh => (st.better_rs_or_better_tu gh).elim (args.better_trans tu_rs) id)

/-- If both `r/s` and `t/u` are best approximations then we're in the ambiguous case. -/
theorem ambiguous_of_rs_and_tu_best
    (rs_best : args.best st.rs) (tu_best : args.best st.tu) : args.ambiguous := by
  -- The only possible case is that r/s and t/u are equidistant from m/n and s = u.
  cases (show args.better st.rs st.tu from rs_best st.tu)
  <;> cases (show args.better st.tu st.rs from tu_best st.rs) <;> try omega
  have s_eq_u : st.s = st.u := by grind only
  have equidistant : args.dist st.rs * st.u = args.dist st.tu * st.s := by grind only
  rw [st.dist_rs, st.dist_tu] at equidistant
  -- From (ts - ru)v = 1 and s = u we get (t - r) v s = 1, hence s = 1
  have htr : (st.t - st.r) * st.v * st.s = 1 := by grind only [st.bracket_det]
  have s_eq_one : st.s = 1 := Int.eq_one_of_mul_eq_one_left (Int.le_of_lt st.s_pos) htr
  -- We have 1 ≤ limit < s + u and s = u = 1, so the limit is 1.
  refine ⟨ by grind only [st.limit_lt_s_add_u, args.one_le_limit], ?_ ⟩
  -- m/n is r + 1/2 if v = 1 and t + 1/2 if v = -1
  cases st.v_cases
  · exact ⟨ st.r, by grind only ⟩
  · exact ⟨ st.t, by grind only ⟩

/-! ## The return value -/

/-- `st.rv` is the return value from limitDenominator - either `r/s` or `t/u`. -/
@[expose] public def rv : args.Candidate := if 2 * st.b * st.u ≤ args.n then st.rs else st.tu

/-- Whichever bound is returned is at least as good as the other one. -/
theorem rv_cases :
    st.rv = st.rs ∧ args.better st.rs st.tu ∨
    st.rv = st.tu ∧ args.better st.tu st.rs := by
  have bu_cs := st.bu_add_cs_eq_n
  rcases Int.lt_or_le (st.c * st.s) (st.b * st.u) with htu | hrs
  · right; refine ⟨ite_eq_right (by grind only), .inl ?_⟩
    grind only [st.dist_rs, st.dist_tu, st.b_eq_rs_cross, st.c_eq_tu_cross]
  · rcases Int.lt_or_eq_of_le hrs with hlt | heq
    · left; refine ⟨ite_eq_left (by grind only), .inl ?_⟩
      grind only [st.dist_rs, st.dist_tu, st.b_eq_rs_cross, st.c_eq_tu_cross]
    · left; refine ⟨ite_eq_left (by grind only), .inr ⟨?_, ?_⟩⟩
      · grind only [st.dist_rs, st.dist_tu, st.c_eq_tu_cross,
          Int.eq_mul_pos args.n_pos st.bracket_det]
      · exact Int.le_of_mul_le_mul_left
          (heq ▸ Int.le_mul_pos st.u_pos st.b_le_c) st.c_pos

/-- The returned candidate is a best approximation. -/
theorem rv_best : args.best st.rv := by
  intro yz
  rcases st.rv_cases with ⟨rveq, hrv⟩ | ⟨rveq, hrv⟩ <;> rw [rveq] <;>
    rcases st.better_rs_or_better_tu yz with h | h <;>
      first | exact h | exact args.better_trans hrv h

/-! ## The ambiguous case -/

section ambiguous

/-
This section studies the special case where the input m/n is a half integer
and limit = 1.
-/

variable (hamb : args.ambiguous)
include hamb

/-- It's convenient to have an oriented version of the definition of half-integer. -/
theorem exists_oriented :
    ∃ w : Int, 2 * args.m * st.v = (2 * w * st.v + 1) * args.n := by
  obtain ⟨w, _⟩ := hamb.2; cases st.v_cases
  · exact ⟨w, by grind only⟩
  · exact ⟨w + 1, by grind only⟩

/- In the ambiguous case both endpoints of the bracket have denominator 1. -/
theorem s_eq_one : st.s = 1 := by grind only [hamb.1, st.s_le_limit, st.s_pos]
theorem u_eq_one : st.u = 1 := by grind only [hamb.1, st.u_le_limit, st.u_pos]

/-- In the ambiguous case, m/n v = r/s v + 1/2. -/
theorem mnv_sub_half :
    2 * args.m * st.s * st.v = (2 * st.r * st.v + st.s) * args.n := by
  -- s = u = 1
  have s_eq_one := st.s_eq_one hamb
  have u_eq_one := st.u_eq_one hamb

  -- rv ≤ m/n v ≤ tv, from the general case
  have : st.r * st.v * args.n ≤ args.m * st.v := by
    grind only [s_eq_one ▸ st.rs_lev_mn]
  have : args.m * st.v ≤ st.t * st.v * args.n := by
    grind only [u_eq_one ▸ st.mn_lev_tu]

  -- there's a w such that m/n v = wv + 1/2, so wv < m/n v < wv + 1
  obtain ⟨w, hw⟩ := st.exists_oriented hamb
  have : w * st.v * args.n < args.m * st.v := by grind only [args.n_pos]
  have : args.m * st.v < (w * st.v + 1) * args.n := by grind only [args.n_pos]

  -- tv = rv + 1 from the determinant condition, and wv < tv and rv < wv + 1 from above
  have : st.t * st.v = st.r * st.v + 1 := by grind only [st.bracket_det]
  have : w * st.v < st.t * st.v := Int.lt_of_lt_mul_pos args.n_pos (by grind only)
  have : st.r * st.v < (w * st.v + 1) := Int.lt_of_lt_mul_pos args.n_pos (by grind only)

  -- hence rv = wv, and the theorem follows
  grind only [show st.r * st.v = w * st.v by omega]

/--
Since t/u v - r/s v = 1/su = 1, it follows immediately that m/n v = t/u v - 1/2.
-/
theorem mnv_add_half : 2 * args.m * st.u * st.v = (2 * st.t * st.v - st.u) * args.n :=
  Int.eq_of_eq_mul_pos st.s_pos (by grind only [
    Int.eq_mul_pos args.n_pos st.bracket_det,
    Int.eq_mul_pos st.u_pos (st.mnv_sub_half hamb),
    st.s_eq_one hamb,
    st.u_eq_one hamb
  ])

/-- So r/s is better than t/u. -/
theorem rs_better_tu : args.better st.rs st.tu := by
  right; grind only [st.dist_rs, st.dist_tu, st.s_eq_one hamb, st.u_eq_one hamb,
    Int.eq_mul_pos st.u_pos (st.mnv_sub_half hamb),
    Int.eq_mul_pos st.s_pos (st.mnv_add_half hamb)]

/-- And t/u is better than r/s. -/
theorem tu_better_rs : args.better st.tu st.rs := by
  right; grind only [st.dist_rs, st.dist_tu, st.s_eq_one hamb, st.u_eq_one hamb,
    Int.eq_mul_pos st.s_pos (st.mnv_add_half hamb),
    Int.eq_mul_pos st.u_pos (st.mnv_sub_half hamb)]

/-- So _both_ r/s and t/u are best approximations. -/
theorem rs_best_and_tu_best : args.best st.rs ∧ args.best st.tu := by
  rcases st.rs_best_or_tu_best with (rs_best | tu_best)
  · exact ⟨ rs_best, fun gh => args.better_trans (st.tu_better_rs hamb) (rs_best gh) ⟩
  · exact ⟨ fun gh => args.better_trans (st.rs_better_tu hamb) (tu_best gh) , tu_best⟩

/--
With the bracket pointing up, `r/s` is `⌊m/n⌋/1` and `t/u` is `(⌊m/n⌋ + 1)/1`.

`s = u = 1` makes both endpoints integers, `bracket_det` makes them adjacent, and
`mnv_sub_half` puts `m/n` midway between them.
-/
theorem endpoints_of_v_eq_one (hv : st.v = 1) :
    st.rs = args.floor ∧ st.tu = args.floorAddOne := by
  have hn := args.n_pos
  have hs := st.s_eq_one hamb
  have hu := st.u_eq_one hamb
  have hdet := st.bracket_det
  have hkey : 2 * args.m = 2 * (st.r * args.n) + args.n := by
    have := st.mnv_sub_half hamb; grind only
  have r_eq : args.m / args.n = st.r := by
    rw [Int.ediv_eq_iff_of_pos hn]; omega
  exact ⟨by grind only [Arguments.floor], by grind only [Arguments.floorAddOne]⟩

/-- And with it pointing down, the two endpoints swap roles. -/
theorem endpoints_of_v_eq_neg_one (hv : st.v = -1) :
    st.rs = args.floorAddOne ∧ st.tu = args.floor := by
  have hn := args.n_pos
  have hs := st.s_eq_one hamb
  have hu := st.u_eq_one hamb
  have hdet := st.bracket_det
  have hkey : 2 * args.m = 2 * (st.r * args.n) - args.n := by
    have := st.mnv_sub_half hamb; grind only
  -- The floor is `r - 1`, so the bounds are stated about `(r - 1) * n`, which `omega`
  -- keeps apart from the `r * n` of `hkey` unless the product is expanded for it.
  have hexp : (st.r - 1) * args.n = st.r * args.n - args.n := by grind only
  have r_eq : args.m / args.n = st.r - 1 := by
    rw [Int.ediv_eq_iff_of_pos hn, hexp]; omega
  exact ⟨by grind only [Arguments.floorAddOne], by grind only [Arguments.floor]⟩

/--
Either way, the two endpoints are `⌊m/n⌋/1` and `(⌊m/n⌋ + 1)/1`. Which of them is which
takes the orientation, and so `v_eq_one`; that the pair is those two does not, which is
what keeps the specification's vocabulary clear of the loop's history.
-/
theorem endpoints_eq_floor_pair :
    (st.rs = args.floor ∧ st.tu = args.floorAddOne)
    ∨ (st.rs = args.floorAddOne ∧ st.tu = args.floor) :=
  st.v_cases.imp (st.endpoints_of_v_eq_one hamb) (st.endpoints_of_v_eq_neg_one hamb)

/-- In the ambiguous case, bu = cs. -/
theorem bu_eq_cs : st.b * st.u = st.c * st.s := by
  grind only [st.b_eq_rs_cross, st.c_eq_tu_cross,
    Int.eq_mul_pos st.u_pos (st.mnv_sub_half hamb),
    Int.eq_mul_pos st.s_pos (st.mnv_add_half hamb)]

/-- In the ambiguous case, v = 1. -/
theorem v_eq_one : st.v = 1 := by
  have s_eq_one := st.s_eq_one hamb
  have u_eq_one := st.u_eq_one hamb
  -- Since s = u = q + ks, (1 - k)s = q, so k ≤ 1.
  have h1 : (1 - st.k) * st.s = st.q := by grind only [u]
  -- Since 0 < a - b and a - kb = c = b, and bu = cs (so b = c), we have 0 < k * b
  have h2 : 0 < st.k * st.b := by grind only [c, st.b_lt_a, st.bu_eq_cs hamb]
  -- It follows from positivity of s and nonnegativity of b that k = 1.
  have : st.k = 1 := by grind only [
    st.s_pos, st.b_nonneg,
    Int.mul_nonneg_iff.mp (h1 ▸ st.q_nonneg), Int.mul_pos_iff.mp h2]
  exact st.v_eq_one_of_q_eq_zero (show st.q = 0 by grind only)

/-- In the ambiguous case r/s = ⌊m/n⌋/1. -/
theorem rs_eq_floor : st.rs = args.floor :=
  (st.endpoints_of_v_eq_one hamb (st.v_eq_one hamb)).1

/-- In the ambiguous case t/u = (⌊m/n⌋ + 1)/1. -/
theorem tu_eq_floor_add_one : st.tu = args.floorAddOne :=
  (st.endpoints_of_v_eq_one hamb (st.v_eq_one hamb)).2

/-- In the ambiguous case r/s is returned. -/
theorem rv_eq_rs : st.rv = st.rs :=
  ite_eq_left (by grind only [st.bu_eq_cs hamb, st.bu_add_cs_eq_n])

/-- In the ambiguous case ⌊m/n⌋ is returned. -/
theorem rv_eq_floor : st.rv = args.floor := by
  rw [st.rv_eq_rs hamb, st.rs_eq_floor hamb]

end ambiguous

end PostLoopState

namespace Arguments

variable (args : Arguments)

/-! # The algorithm -/

/-- The state on exit from the loop, run from the initial state. -/
@[expose] public def postLoopState : PostLoopState args :=
  let loopState := LoopState.initialLoopState args
  ⟨loopState.runLoop, loopState.runLoop_loopCondition_false⟩

/-- The full algorithm, end to end. -/
@[expose] public def limitDenominator : args.Candidate := args.postLoopState.rv

/-! # Results -/

/-! ## Uniqueness of best approximations -/

/-- Outside the ambiguous case, any two best approximations are equal. -/
theorem non_ambiguous_best (not_amb : ¬ args.ambiguous) {ef gh : args.Candidate}
    (hef : args.best ef) (hgh : args.best gh) : ef = gh := by
  let st := args.postLoopState
  cases st.eq_rs_or_eq_tu_of_best hef <;> cases st.eq_rs_or_eq_tu_of_best hgh
  <;> grind only [st.ambiguous_of_rs_and_tu_best]

/-- In the ambiguous case, the best approximations are exactly ⌊m/n⌋ and ⌊m/n⌋ + 1. -/
theorem ambiguous_best (hamb : args.ambiguous) {yz : args.Candidate} :
    args.best yz ↔ yz = args.floor ∨ yz = args.floorAddOne := by
  let st := args.postLoopState
  obtain ⟨rs_best, tu_best⟩ := st.rs_best_and_tu_best hamb
  have hpair : (yz = st.rs ∨ yz = st.tu) ↔ (yz = args.floor ∨ yz = args.floorAddOne) := by
    rcases st.endpoints_eq_floor_pair hamb with ⟨hrs, htu⟩ | ⟨hrs, htu⟩
    · rw [hrs, htu]
    · rw [hrs, htu]; exact Or.comm
  rw [← hpair]
  constructor
  · exact st.eq_rs_or_eq_tu_of_best
  · rintro (rfl | rfl)
    · exact rs_best
    · exact tu_best

/-! ## Any best approximation is reduced -/

/-- A best approximation is one of the two bracket endpoints, and both of those are in
lowest terms. -/
theorem isReduced_of_best {ef : args.Candidate} (hef : args.best ef) :
    ef.isReduced := by
  let st := args.postLoopState
  rcases st.eq_rs_or_eq_tu_of_best hef with rfl | rfl
  · exact st.isReduced_rs
  · exact st.isReduced_tu

/-! ## The return value -/

/-- The limitDenominator return value is always a best approximation. -/
public theorem limitDenominator_best : args.best args.limitDenominator :=
  args.postLoopState.rv_best

/-- In the ambiguous case, ⌊m/n⌋ is returned. -/
public theorem limitDenominator_ambiguous_case (hamb : args.ambiguous) :
    args.limitDenominator = args.floor :=
  args.postLoopState.rv_eq_floor hamb

end Arguments

/-! # The specification -/

/-
Everything above is in the proofs' own vocabulary. This section is where it meets the
specification's, and the only part of the file that mentions `isBestApproximation`.
-/

/--
`best` and `isBestApproximation` say the same thing of the same pair.

`better`'s two arms are the specification's two clauses. Forwards, either arm gives the
closeness clause, and the strict arm is impossible once the rival is at least as close, so
the tie arm supplies the denominator comparison. Backwards, a strict inequality is the
first arm and an equality feeds the second clause, which gives the second arm.
-/
public theorem best_iff_isBestApproximation {args : Arguments} (ef : args.Candidate) :
    args.best ef ↔ isBestApproximation args.m args.n args.limit ef.num ef.den := by
  constructor
  · intro hbest
    refine ⟨ef.pos, ef.den_limited, fun y z hz hzl => ?_⟩
    have hb := hbest ⟨y, z, hz, hzl⟩
    simp only [Arguments.better, Arguments.dist] at hb
    unfold atLeastAsClose
    omega
  · rintro ⟨-, -, hall⟩ gh
    have hc := hall gh.num gh.den gh.pos gh.den_limited
    unfold atLeastAsClose at hc
    simp only [Arguments.better, Arguments.dist]
    omega

/-- `Arguments.ambiguous` is the specification's `isAmbiguous`, formula for formula. -/
public theorem ambiguous_iff_isAmbiguous (args : Arguments) :
    args.ambiguous ↔ isAmbiguous args.m args.n args.limit := Iff.rfl

/--
Outside the ambiguous case the specification determines the answer: no two distinct pairs
satisfy it.
-/
public theorem isBestApproximation_unique_of_not_ambiguous {m n l r₁ s₁ r₂ s₂ : Int}
    (hn : 0 < n) (hamb : ¬ isAmbiguous m n l)
    (h₁ : isBestApproximation m n l r₁ s₁) (h₂ : isBestApproximation m n l r₂ s₂) :
    r₁ = r₂ ∧ s₁ = s₂ := by
  have hl : 1 ≤ l := by have := h₁.1; have := h₁.2.1; omega
  let args : Arguments := ⟨m, n, l, hn, hl⟩
  let ef : args.Candidate := ⟨r₁, s₁, h₁.1, h₁.2.1⟩
  let gh : args.Candidate := ⟨r₂, s₂, h₂.1, h₂.2.1⟩
  have heq : ef = gh :=
    args.non_ambiguous_best (fun ha => hamb ((ambiguous_iff_isAmbiguous args).mp ha))
      ((best_iff_isBestApproximation ef).mpr h₁) ((best_iff_isBestApproximation gh).mpr h₂)
  exact ⟨congrArg Arguments.Candidate.num heq, congrArg Arguments.Candidate.den heq⟩

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
    let ef : args.Candidate := ⟨r, s, h.1, h.2.1⟩
    rcases (args.ambiguous_best hamb (yz := ef)).mp ((best_iff_isBestApproximation ef).mpr h)
      with he | he
    · exact Or.inl (congrArg (fun c : args.Candidate => (c.num, c.den)) he)
    · exact Or.inr (congrArg (fun c : args.Candidate => (c.num, c.den)) he)
  · intro h
    have hfloor := (best_iff_isBestApproximation args.floor).mp
      ((args.ambiguous_best hamb).mpr (Or.inl rfl))
    have hadd := (best_iff_isBestApproximation args.floorAddOne).mp
      ((args.ambiguous_best hamb).mpr (Or.inr rfl))
    rcases h with he | he <;> rw [Prod.mk.injEq] at he <;> rw [he.1, he.2]
    · exact hfloor
    · exact hadd

/--
The result is in lowest terms, and that is a consequence of the specification rather than
a part of it.

A pair satisfying the specification is one of the two bracket endpoints, and the bracket's
determinant is a Bézout identity for each of them.
-/
public theorem isBestApproximation.gcd_eq_one {m n l r s : Int} (hn : 0 < n)
    (h : isBestApproximation m n l r s) : Int.gcd r s = 1 := by
  have hl : 1 ≤ l := by have := h.1; have := h.2.1; omega
  let args : Arguments := ⟨m, n, l, hn, hl⟩
  let ef : args.Candidate := ⟨r, s, h.1, h.2.1⟩
  obtain ⟨g, k, hb⟩ := args.isReduced_of_best ((best_iff_isBestApproximation ef).mpr h)
  exact Int.gcd_eq_one_of_bezout hb
