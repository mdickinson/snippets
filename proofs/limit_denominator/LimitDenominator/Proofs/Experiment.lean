/-

To do
-----

- prove that s = u implies l = 1 and m/n a half-integer

-/

module

theorem Int.le_mul_of_one_le_left {a b : Int} (ha : 0 ≤ a) (hb : 1 ≤ b) : a ≤ b * a := by
  grind only [Int.mul_le_mul_of_nonneg_right hb ha]

def Int.abs (a : Int) : Int := if 0 ≤ a then a else -a

theorem Int.abs_of_nonneg {a : Int} (ha : 0 ≤ a) : a.abs = a := by grind only [Int.abs]
theorem Int.abs_of_nonpos {a : Int} (ha : a ≤ 0) : a.abs = -a := by grind only [Int.abs]
theorem Int.abs_pos_of_ne_zero {a : Int} : a ≠ 0 → 0 < a.abs := by grind only [Int.abs]
theorem Int.abs_ne_zero_of_ne_zero {a : Int} : a ≠ 0 → a.abs ≠ 0 := by grind only [Int.abs]
theorem Int.abs_mul (a b : Int) : (a * b).abs = a.abs * b.abs := by
  rcases Int.le_total 0 a with h1 | h2 <;> rcases Int.le_total 0 b with h3 | h4
  · rw [Int.abs_of_nonneg h1, Int.abs_of_nonneg h3, Int.abs_of_nonneg (Int.mul_nonneg h1 h3)]
  · rw [Int.abs_of_nonneg h1, Int.abs_of_nonpos h4, Int.abs_of_nonpos (Int.mul_nonpos_of_nonneg_of_nonpos h1 h4)]
    grind only
  · rw [Int.abs_of_nonpos h2, Int.abs_of_nonneg h3, Int.abs_of_nonpos (Int.mul_nonpos_of_nonpos_of_nonneg h2 h3)]
    grind only
  · rw [Int.abs_of_nonpos h2, Int.abs_of_nonpos h4, Int.abs_of_nonneg (Int.mul_nonneg_of_nonpos_of_nonpos h2 h4)]
    grind only

/-- A fraction, minus the lowest terms hypothesis. -/
structure FractionPair where (num : Int) {den : Int} (pos : 0 < den)

namespace FractionPair

variable (ef : FractionPair) {a b : Int}

/-- We sometimes just need nonnegativity or nonzeroness. -/
theorem nonneg : 0 ≤ ef.den := Int.le_of_lt ef.pos
theorem nonzero : ef.den ≠ 0 := Int.ne_of_gt ef.pos

/-
Proofs below often involve either multiplying both sides of an (in)equality
by a denominator or cancelling a denominator from both sides. The following
lemmas help with those operations.
-/
theorem eq_by_den (h : a = b) : a * ef.den = b * ef.den := by rw [h]
theorem lt_by_den (h : a < b) : a * ef.den < b * ef.den :=
  Int.mul_lt_mul_of_pos_right h ef.pos
theorem le_by_den (h : a ≤ b) : a * ef.den ≤ b * ef.den :=
  Int.mul_le_mul_of_nonneg_right h ef.nonneg
theorem of_eq_by_den (h : a * ef.den = b * ef.den) : a = b :=
  Int.eq_of_mul_eq_mul_right ef.nonzero h
theorem of_lt_by_den (h : a * ef.den < b * ef.den) : a < b :=
  Int.lt_of_mul_lt_mul_right h ef.nonneg
theorem of_le_by_den (h : a * ef.den ≤ b * ef.den) : a ≤ b :=
  Int.le_of_mul_le_mul_right h ef.pos

end FractionPair

/-- State on exiting the loop. -/
structure PostLoopState where
  mn : FractionPair
  l : Int
  hl : 0 < l
  rs : FractionPair
  tu : FractionPair
  v : Int
  det : (tu.num * rs.den - rs.num * tu.den) * v = 1
  hrs : rs.den ≤ l
  hrt : tu.den ≤ l
  hsu : l < rs.den + tu.den
  rs_lev_mn : rs.num * mn.den * v ≤ mn.num * rs.den * v
  mn_lev_mediant : mn.num * (rs.den + tu.den) * v ≤ (rs.num + tu.num) * mn.den * v

namespace PostLoopState

variable (st : PostLoopState)

/-- The return value from limit_denominator. -/
def rv : FractionPair :=
  if
    (st.mn.num * st.rs.den - st.rs.num * st.mn.den) * st.v * st.tu.den
    ≤ (st.tu.num * st.mn.den - st.mn.num * st.tu.den) * st.v * st.rs.den
  then st.rs else st.tu

/-- That st.v is nonzero follows immediately from st.det. -/
theorem v_nonzero : st.v ≠ 0 := by grind only [st.det]

/-- m/n ≤ t/u (orientation aware). -/
theorem mn_lev_tu : st.mn.num * st.tu.den * st.v ≤ st.tu.num * st.mn.den * st.v :=
  Int.le_of_mul_le_mul_right
    (by grind only [st.mn.pos, st.mn.eq_by_den st.det, st.tu.le_by_den st.mn_lev_mediant])
    (Int.add_pos st.rs.pos st.tu.pos)

/- Generic fraction pairs. -/
variable (ef gh ij : FractionPair)

/-- e/f ≤ g/h, taking into account the state orientation. -/
def lev := ef.num * gh.den * st.v ≤ gh.num * ef.den * st.v

/-- e/f is closer to st.mn than g/h is. -/
def closer := ((ef.num * st.mn.den - st.mn.num * ef.den) * st.v).abs * gh.den
    < ((gh.num * st.mn.den - st.mn.num * gh.den) * st.v).abs * ef.den

/-- e/f and g/h are equidistant from st.mn. -/
def disteq := ((ef.num * st.mn.den - st.mn.num * ef.den) * st.v).abs * gh.den
    = ((gh.num * st.mn.den - st.mn.num * gh.den) * st.v).abs * ef.den

/- Redeclare generic fractions as implicit. -/
variable {ef gh ij : FractionPair}

/-- if e/f ≤ g/h and g/h ≤ i/j then e/f ≤ i/j (orientation aware) -/
theorem lev_trans (h1 : st.lev ef gh) (h2 : st.lev gh ij) : st.lev ef ij :=
  gh.of_le_by_den (by grind only [ij.le_by_den h1, ef.le_by_den h2])

theorem disteq_trans (h1 : st.disteq ef gh) (h2 : st.disteq gh ij) : st.disteq ef ij :=
  gh.of_eq_by_den (by grind only [ij.eq_by_den h1, ef.eq_by_den h2])

theorem closer_of_closer_of_disteq
    (h1 : st.closer ef gh) (h2 : st.disteq gh ij) : st.closer ef ij :=
  gh.of_lt_by_den (by grind only [ij.lt_by_den h1, ef.eq_by_den h2])

theorem closer_of_disteq_of_closer
    (h1 : st.disteq ef gh) (h2 : st.closer gh ij) : st.closer ef ij :=
  gh.of_lt_by_den (by grind only [ij.eq_by_den h1, ef.lt_by_den h2])

theorem closer_trans (h1 : st.closer ef gh) (h2 : st.closer gh ij) : st.closer ef ij :=
  gh.of_lt_by_den (by grind only [ij.lt_by_den h1, ef.lt_by_den h2])

theorem abs_diff_of_lev (h : st.lev ef gh) :
    ((ef.num * gh.den - gh.num * ef.den) * st.v).abs =
    (gh.num * ef.den - ef.num * gh.den) * st.v := by
  grind only [lev, Int.abs_of_nonpos]

theorem abs_diff_of_lev' (h : st.lev ef gh) :
    ((gh.num * ef.den - ef.num * gh.den) * st.v).abs =
    (gh.num * ef.den - ef.num * gh.den) * st.v := by
  grind only [lev, Int.abs_of_nonneg]

/-- If a linear combination of s and u is positive, one of the coefficients is. -/
theorem lc_pos {a b : Int} : 0 < a * st.rs.den + b * st.tu.den → 0 < a ∨ 0 < b := by
  intro; rcases (show 0 < a * st.rs.den ∨ 0 < b * st.tu.den by grind only) with h1 | h2
  · left; exact Int.pos_of_mul_pos_left h1 st.rs.pos
  · right; exact Int.pos_of_mul_pos_left h2 st.tu.pos

/-- A fraction pair with denominator ≤ l must be outside the bracket. -/
theorem loop_or_extended {yz : FractionPair} (hyz : yz.den ≤ st.l):
    st.lev yz st.rs ∨ st.lev st.tu yz := by
  have lc : 0 < (1 - (st.tu.num * yz.den - yz.num * st.tu.den) * st.v) * st.rs.den
      + (1 - (yz.num * st.rs.den - st.rs.num * yz.den) * st.v) * st.tu.den := by
    grind only [yz.eq_by_den st.det, st.hsu]
  cases st.lc_pos lc
  · right; grind only [lev]
  · left; grind only [lev]

/-- The four possible cases for a candidate fraction pair. -/
theorem yz_cases {yz : FractionPair} (hyz : yz.den ≤ st.l) :
    st.closer st.rs yz
    ∨ st.disteq st.rs yz ∧ st.rs.den ≤ yz.den
    ∨ st.disteq st.tu yz ∧ st.tu.den ≤ yz.den
    ∨ st.closer st.tu yz := by
  dsimp only [closer, disteq]
  rcases loop_or_extended st hyz with hloop | hextended
  · rcases Int.lt_or_eq_of_le hloop with hbl | hatl
    · left
      rw [st.abs_diff_of_lev st.rs_lev_mn]
      rw [st.abs_diff_of_lev (st.lev_trans (Int.le_of_lt hbl) st.rs_lev_mn)]
      grind only [st.mn.lt_by_den hbl]
    · right; left; constructor
      · rw [st.abs_diff_of_lev st.rs_lev_mn]
        rw [st.abs_diff_of_lev (st.lev_trans (Int.le_of_eq hatl) st.rs_lev_mn)]
        grind only [st.mn.eq_by_den hatl]
      · have : yz.den = (st.tu.num * yz.den - yz.num * st.tu.den) * st.v * st.rs.den := by
          grind only [yz.eq_by_den st.det, st.tu.eq_by_den hatl]
        exact this ▸ (Int.le_mul_of_one_le_left
          st.rs.nonneg (Int.pos_of_mul_pos_left (this ▸ yz.pos) st.rs.pos))
  · rcases Int.lt_or_eq_of_le hextended with hbe | hate
    · right; right; right
      rw [st.abs_diff_of_lev' st.mn_lev_tu]
      rw [st.abs_diff_of_lev' (st.lev_trans st.mn_lev_tu (Int.le_of_lt hbe))]
      grind only [st.mn.lt_by_den hbe]
    · right; right; left; constructor
      · rw [st.abs_diff_of_lev' st.mn_lev_tu]
        rw [st.abs_diff_of_lev' (st.lev_trans st.mn_lev_tu (Int.le_of_eq hate))]
        grind only [st.mn.eq_by_den hate]
      · have : yz.den = (yz.num * st.rs.den - st.rs.num * yz.den) * st.v * st.tu.den :=
          by grind only [yz.eq_by_den st.det, st.rs.eq_by_den hate]
        exact this ▸ (Int.le_mul_of_one_le_left
          st.tu.nonneg (Int.pos_of_mul_pos_left (this ▸ yz.pos) st.tu.pos))

/-- The three possible output cases. -/
theorem rv_cases :
    (st.rv = st.rs ∧ st.closer st.rs st.tu)
    ∨ st.rv = st.rs ∧ st.disteq st.rs st.tu ∧ st.rs.den ≤ st.tu.den
    ∨ st.rv = st.tu ∧ st.closer st.tu st.rs := by
  let b := (st.mn.num * st.rs.den - st.rs.num * st.mn.den) * st.v
  let c := (st.tu.num * st.mn.den - st.mn.num * st.tu.den) * st.v
  unfold closer disteq
  rcases Int.lt_or_le (c * st.rs.den) (b * st.tu.den) with h1 | hloop
  · right; right; refine ⟨if_neg (Int.not_le_of_gt h1), ?_⟩
    rw [st.abs_diff_of_lev st.rs_lev_mn, st.abs_diff_of_lev' (st.mn_lev_tu)]
    exact h1
  · rcases Int.lt_or_eq_of_le hloop with hlt | heq
    · left; refine ⟨if_pos hloop, ?_⟩
      rw [st.abs_diff_of_lev st.rs_lev_mn, st.abs_diff_of_lev' (st.mn_lev_tu)]
      exact hlt
    · right; left; refine ⟨if_pos hloop, ?_, ?_⟩
      · rw [st.abs_diff_of_lev st.rs_lev_mn, st.abs_diff_of_lev' (st.mn_lev_tu)]
        exact heq
      · have cs_pos : 0 < c * st.rs.den := by
          grind only [st.mn.eq_by_den st.det, st.mn.pos]
        have cs_le_cu : c * st.rs.den ≤ c * st.tu.den := by
          grind only [st.tu.le_by_den st.mn_lev_mediant]
        exact Int.le_of_mul_le_mul_left cs_le_cu
          (Int.pos_of_mul_pos_left cs_pos st.rs.pos)

/-- The twelve combinations. -/
theorem rv_is_best {yz : FractionPair} (hyz : yz.den ≤ st.l) :
    st.closer st.rv yz ∨ st.disteq st.rv yz ∧ st.rv.den ≤ yz.den := by
  rcases st.yz_cases hyz with hbl | ⟨hatl, s_le_z⟩ | ⟨hate, u_le_z⟩ | hbe
    <;> rcases st.rv_cases with ⟨rveq, hcloser⟩ | ⟨rveq, heq, s_le_u⟩ | ⟨rveq, hcloser⟩
    <;> rw [rveq]
  · left; exact hbl
  · left; exact hbl
  · left; exact st.closer_trans hcloser hbl
  · right; exact ⟨ hatl, s_le_z ⟩
  · right; exact ⟨ hatl, s_le_z ⟩
  · left; exact st.closer_of_closer_of_disteq hcloser hatl
  · left; exact st.closer_of_closer_of_disteq hcloser hate
  · right; exact ⟨ st.disteq_trans heq hate, Int.le_trans s_le_u u_le_z ⟩
  · right; exact ⟨ hate, u_le_z ⟩
  · left; exact st.closer_trans hcloser hbe
  · left; exact st.closer_of_disteq_of_closer heq hbe
  · left; exact hbe

/-- Translation into more natural definitions of closer and disteq. -/

def closer2 (st : PostLoopState) (rs : FractionPair) (yz : FractionPair) :=
  (rs.num * st.mn.den - st.mn.num * rs.den).abs * yz.den
  < (yz.num * st.mn.den - st.mn.num * yz.den).abs * rs.den

def disteq2 (st : PostLoopState) (rs : FractionPair) (yz : FractionPair) :=
  (rs.num * st.mn.den - st.mn.num * rs.den).abs * yz.den
  = (yz.num * st.mn.den - st.mn.num * yz.den).abs * rs.den

theorem closer2_iff_closer
    (rs : FractionPair) (yz : FractionPair) :
    st.closer2 rs yz ↔ st.closer rs yz := by
  unfold closer2 closer
  simp only [Int.abs_mul, Int.mul_right_comm _ st.v.abs]
  exact (Int.mul_lt_mul_right (Int.abs_pos_of_ne_zero st.v_nonzero)).symm

theorem disteq2_iff_disteq
    (rs : FractionPair) (yz : FractionPair) :
    st.disteq2 rs yz ↔ st.disteq rs yz := by
  unfold disteq2 disteq
  simp only [Int.abs_mul, Int.mul_right_comm _ st.v.abs]
  exact (Int.mul_eq_mul_right_iff (Int.abs_ne_zero_of_ne_zero st.v_nonzero)).symm

theorem rv_is_best2 {yz : FractionPair} (hyz : yz.den ≤ st.l) :
    st.closer2 st.rv yz ∨ st.disteq2 st.rv yz ∧ st.rv.den ≤ yz.den := by
  rw [st.closer2_iff_closer, st.disteq2_iff_disteq]
  exact st.rv_is_best hyz

end PostLoopState
