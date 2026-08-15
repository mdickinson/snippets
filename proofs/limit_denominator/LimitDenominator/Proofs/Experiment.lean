module

/-! # Support lemmas -/

theorem Int.le_mul_of_one_le_left {a b : Int} (ha : 0 ≤ a) (hb : 1 ≤ b) :
    a ≤ b * a := by grind only [Int.mul_le_mul_of_nonneg_right hb ha]

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

/- Another support lemma. -/
theorem Int.eq_one_or_neg_one_of_mul_eq_one (a b : Int) (hab : a * b = 1) :
    b = 1 ∨ b = -1 := by
  rw [← Int.abs_eq b (by decide)]
  exact Int.eq_one_of_mul_eq_one_left (Int.abs_nonneg b)
    (show a.abs * b.abs = 1 by grind only [Int.abs_mul a b, Int.abs])

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

/-- A fraction pair is a half integer if it has the form k + 1/2 for some k. -/
def isHalfInteger := ∃ (k : Int), (2 * ef.num - ef.den) = 2 * ef.den * k

end FractionPair

/-! # Post-loop analysis -/

/-
The `PostLoopState` structure represents the state of knowledge on exiting the loop: we
have fraction pairs r/s and t/u (a Farey pair) bracketing the target fraction pair m/n;
we know that both r/s and t/u have "small" denominator (s ≤ l and u ≤ l), but that s + u
exceeds our denominator limit (s + u > l), and it follows that everything strictly
between `r/s` and `t/u` has denominator exceeding `l`. (We prove the contrapositive
of this below, as `lev_rs_or_tu_lev`: any fraction pair with denominator no larger
than `l` must be outside the bracket, or equal to one or other of the endpoints.)

The field `v` represents the orientation of the bracket, and from `det` it must
be either `1` or `-1`. If `v = 1` then we have

    r/s ≤ m/n < t/u

and if `v = -1` then we have

    t/u < m/n ≤ r/s

From the loop exit condition and the way that `t/u` was constructed, we further know
that in fact `m/n ≤ (r + t)/(s + u)` in case `v = 1` and `(r + t)/(s + u) ≤ m/n` in case
`v = -1`, so `m/n` is in fact bracketed by the Farey pair `r/s` and `(r + t)/(s + u)`.
`rs_lev_mn` and `mn_lev_mediant` are the two relevant statements. We derive the fact
that `m/n < t/u` (`v = 1`) or `t/u < m/n` (`v = -1`) as a consequence: `mn_lev_tu`.

The `tie` field records behaviour of the loop in the special case where `l = 1`
and `m/n` is a half integer. This is the only case where r/s and t/u can be
equidistant from m/n with the same denominator.
-/

/-- State on exiting the loop. -/
structure PostLoopState where
  mn : FractionPair
  rs : FractionPair
  tu : FractionPair
  l : Int
  v : Int
  det : (tu.num * rs.den - rs.num * tu.den) * v = 1
  hrs : rs.den ≤ l
  htu : tu.den ≤ l
  hsu : l < rs.den + tu.den
  rs_lev_mn : rs.num * mn.den * v ≤ mn.num * rs.den * v
  mn_lev_mediant : mn.num * (rs.den + tu.den) * v ≤ (rs.num + tu.num) * mn.den * v
  tie : l = 1 ∧ mn.isHalfInteger → rs.num < tu.num

namespace PostLoopState

/-
We let `st` represent the post-loop state throughout this section. We also define
shortcuts to the various numerators and denominators and definitions for `b` and `c`.
-/
variable (st : PostLoopState)
abbrev m := st.mn.num
abbrev n := st.mn.den
abbrev r := st.rs.num
abbrev s := st.rs.den
abbrev t := st.tu.num
abbrev u := st.tu.den

abbrev b := (st.m * st.s - st.r * st.n) * st.v
abbrev c := (st.t * st.n - st.m * st.u) * st.v

/-- `st.rv` is the return value from limit_denominator. -/
def rv : FractionPair := if 2 * st.b * st.u ≤ st.n then st.rs else st.tu

/-- m/n ≤ t/u if v = 1, and t/u ≤ m/n if v = -1. -/
theorem mn_lev_tu : st.m * st.u * st.v ≤ st.t * st.n * st.v :=
  Int.le_of_mul_le_mul_right
    (by grind only [
      st.mn.pos, st.mn.eq_mul_den st.det, st.tu.le_mul_den st.mn_lev_mediant])
    (Int.add_pos st.rs.pos st.tu.pos)

/-- v must be either 1 or -1.-/
theorem v_cases : st.v = 1 ∨ st.v = -1 := Int.eq_one_or_neg_one_of_mul_eq_one _ _ st.det

/- Generic fraction pairs. -/
variable (ef gh ij : FractionPair)

/--
We define `st.lev` as an orientation-aware less-than-or-equal-to relation:
`st.lev ef gh` means `e/f ≤ g/h` if `st.v = 1`, and `g/h ≤ e/f` if `st.v = -1`.
-/
def lev := ef.num * gh.den * st.v ≤ gh.num * ef.den * st.v

/-- The st.lev relation is transitive. -/
theorem lev_trans {ef gh ij : FractionPair}
    (h1 : st.lev ef gh) (h2 : st.lev gh ij) : st.lev ef ij :=
  gh.le_of_le_mul_den (by grind only [ij.le_mul_den h1, ef.le_mul_den h2])

/-- Scaled distance from e/f to m/n. -/
def dist := (ef.num * st.n - st.m * ef.den).abs

/-- Distance for values ≤ m/n. -/
theorem dist_of_lev_mn {ef : FractionPair} (h : st.lev ef st.mn) :
    st.dist ef = (st.m * ef.den - ef.num * st.n) * st.v := by
  have rhs_nonneg : 0 ≤ (st.m * ef.den - ef.num * st.n) * st.v := by
    grind only [lev, st.v_cases]
  grind only [dist, Int.abs_eq _ rhs_nonneg, st.v_cases]

/-- Distance for values ≥ m/n. -/
theorem dist_of_mn_lev {ef : FractionPair} (h : st.lev st.mn ef) :
    st.dist ef = (ef.num * st.n - st.m * ef.den) * st.v := by
  have rhs_nonneg : 0 ≤ (ef.num * st.n - st.m * ef.den) * st.v := by
    grind only [lev, st.v_cases]
  grind only [dist, Int.abs_eq _ rhs_nonneg, st.v_cases]

/-
Given two approximations e/f and g/h to m/n, we say that e/f is *better* than g/h
if either:

- e/f is closer to m/n than g/h is, or
- e/f and g/h are equidistant from m/n, but f ≤ h.

Note the slight abuse of language: "better" suggests a non-reflexive relation, but
our "better" relation is reflexive: e/f is better than itself.
-/

/-- e/f is a better approximation to m/n than g/h is. -/
def better :=
  st.dist ef * gh.den < st.dist gh * ef.den
  ∨
  st.dist ef * gh.den = st.dist gh * ef.den ∧ ef.den ≤ gh.den

/- Redeclare generic fractions as implicit. -/
variable {ef gh ij : FractionPair}

/-- The "better" relation is transitive. -/
theorem better_trans (h1 : st.better ef gh) (h2 : st.better gh ij) :
    st.better ef ij := by
  rcases h1 with h1 | ⟨h1, d1⟩ <;> rcases h2 with h2 | ⟨h2, d2⟩
  · left; exact gh.lt_of_lt_mul_den (by grind only [ij.lt_mul_den h1, ef.lt_mul_den h2])
  · left; exact gh.lt_of_lt_mul_den (by grind only [ij.lt_mul_den h1, ef.eq_mul_den h2])
  · left; exact gh.lt_of_lt_mul_den (by grind only [ij.eq_mul_den h1, ef.lt_mul_den h2])
  · right
    exact ⟨gh.eq_of_eq_mul_den (by grind only [ij.eq_mul_den h1, ef.eq_mul_den h2]),
      Int.le_trans d1 d2⟩

/-- If a linear combination of s and u is positive, one of the coefficients is. -/
theorem lc_pos {a b : Int} : 0 < a * st.s + b * st.u → 0 < a ∨ 0 < b := by
  intro; rcases (show 0 < a * st.s ∨ 0 < b * st.u by grind only) with h1 | h2
  · left; exact Int.pos_of_mul_pos_left h1 st.rs.pos
  · right; exact Int.pos_of_mul_pos_left h2 st.tu.pos

/-- A fraction pair with denominator ≤ l must be outside the bracket. -/
theorem lev_rs_or_tu_lev {yz : FractionPair} (hyz : yz.den ≤ st.l):
    st.lev yz st.rs ∨ st.lev st.tu yz := by
  have lc : 0 < (1 - (st.t * yz.den - yz.num * st.u) * st.v) * st.s
      + (1 - (yz.num * st.s - st.r * yz.den) * st.v) * st.u := by
    grind only [yz.eq_mul_den st.det, st.hsu]
  cases st.lc_pos lc
  · right; grind only [lev]
  · left; grind only [lev]

/-- One of the two candidates is at least as good as any candidate fraction pair. -/
theorem yz_cases {yz : FractionPair} (hyz : yz.den ≤ st.l) :
    st.better st.rs yz ∨ st.better st.tu yz := by
  rcases lev_rs_or_tu_lev st hyz with hrs | htu
  · rcases Int.lt_or_eq_of_le hrs with hbl | hatl
    · left; left
      rw [st.dist_of_lev_mn st.rs_lev_mn]
      rw [st.dist_of_lev_mn (st.lev_trans (Int.le_of_lt hbl) st.rs_lev_mn)]
      grind only [st.mn.lt_mul_den hbl]
    · left; right; constructor
      · rw [st.dist_of_lev_mn st.rs_lev_mn]
        rw [st.dist_of_lev_mn (st.lev_trans (Int.le_of_eq hatl) st.rs_lev_mn)]
        grind only [st.mn.eq_mul_den hatl]
      · have : yz.den = (st.t * yz.den - yz.num * st.u) * st.v * st.s := by
          grind only [yz.eq_mul_den st.det, st.tu.eq_mul_den hatl]
        exact this ▸ (Int.le_mul_of_one_le_left
          st.rs.nonneg (Int.pos_of_mul_pos_left (this ▸ yz.pos) st.rs.pos))
  · rcases Int.lt_or_eq_of_le htu with hbe | hate
    · right; left
      rw [st.dist_of_mn_lev st.mn_lev_tu]
      rw [st.dist_of_mn_lev (st.lev_trans st.mn_lev_tu (Int.le_of_lt hbe))]
      grind only [st.mn.lt_mul_den hbe]
    · right; right; constructor
      · rw [st.dist_of_mn_lev st.mn_lev_tu]
        rw [st.dist_of_mn_lev (st.lev_trans st.mn_lev_tu (Int.le_of_eq hate))]
        grind only [st.mn.eq_mul_den hate]
      · have : yz.den = (yz.num * st.s - st.r * yz.den) * st.v * st.u :=
          by grind only [yz.eq_mul_den st.det, st.rs.eq_mul_den hate]
        exact this ▸ (Int.le_mul_of_one_le_left
          st.tu.nonneg (Int.pos_of_mul_pos_left (this ▸ yz.pos) st.tu.pos))

/-- The returned pair is at least as good as the other. -/
theorem rv_cases :
    st.rv = st.rs ∧ st.better st.rs st.tu ∨ st.rv = st.tu ∧ st.better st.tu st.rs := by
  have hn := st.mn.eq_mul_den st.det
  rcases Int.lt_or_le (st.c * st.s) (st.b * st.u) with h1 | hrs
  · right; refine ⟨if_neg (by grind only), .inl ?_⟩
    rw [st.dist_of_lev_mn st.rs_lev_mn, st.dist_of_mn_lev st.mn_lev_tu]
    exact h1
  · rcases Int.lt_or_eq_of_le hrs with hlt | heq
    · left; refine ⟨if_pos (by grind only), .inl ?_⟩
      rw [st.dist_of_lev_mn st.rs_lev_mn, st.dist_of_mn_lev st.mn_lev_tu]
      exact hlt
    · left; refine ⟨if_pos (by grind only), .inr ⟨?_, ?_⟩⟩
      · rw [st.dist_of_lev_mn st.rs_lev_mn, st.dist_of_mn_lev st.mn_lev_tu]
        exact heq
      · have cs_pos : 0 < st.c * st.s := by
          grind only [st.mn.eq_mul_den st.det, st.mn.pos]
        have cs_le_cu : st.c * st.s ≤ st.c * st.u := by
          grind only [st.tu.le_mul_den st.mn_lev_mediant]
        exact Int.le_of_mul_le_mul_left cs_le_cu
          (Int.pos_of_mul_pos_left cs_pos st.rs.pos)

/-- The returned fraction pair has denominator bounded by l. -/
theorem rv_bounded : st.rv.den ≤ st.l := by grind only [rv, st.hrs, st.htu]

/-- The returned fraction pair is better than any candidate. -/
theorem rv_is_best {yz : FractionPair} (hyz : yz.den ≤ st.l) : st.better st.rv yz := by
  rcases st.rv_cases with ⟨rveq, hrv⟩ | ⟨rveq, hrv⟩
    <;> rw [rveq] <;> rcases st.yz_cases hyz with h | h
  · exact h
  · exact st.better_trans hrv h
  · exact st.better_trans hrv h
  · exact h

/--
Tie case: if r/s is better than t/u and t/u is better than r/s, then l = 1 and
m/n is a half integer.
-/
theorem rv_tie_case (h1 : st.better st.rs st.tu) (h2 : st.better st.tu st.rs) :
    st.l = 1 ∧ st.mn.isHalfInteger := by
  /- The try omega eliminates 3 out of the 4 cases immediately as impossible. -/
  cases h1 <;> cases h2 <;> try omega
  /- We're left with the case where r/s and t/u are equidistant and s = u. -/
  have hbc : st.b * st.s = st.c * st.u := by
    grind only [st.dist_of_lev_mn st.rs_lev_mn, st.dist_of_mn_lev st.mn_lev_tu]
  have htr : (st.t - st.r) * st.v * st.s = 1 := by grind only [st.det]
  have hs : st.s = 1 := Int.eq_one_of_mul_eq_one_left st.rs.nonneg htr
  refine ⟨ by grind only [st.hrs, st.htu, st.hsu], ?_ ⟩
  cases st.v_cases
  · exact ⟨st.r, by grind only⟩
  · exact ⟨st.r - 1, by grind only⟩

end PostLoopState
