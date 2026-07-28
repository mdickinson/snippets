module

public import LimitDenominator.Proofs.AfterLoop

/-!
The bracket, transcribing the informal proof's § "Proof overview".

Every candidate strictly inside the bracket has denominator exceeding the limit, so every
candidate the specification quantifies over lies on one side or the other; and a candidate on a
given side is no closer to the target than that side's candidate is.

Three quantities recur below, always written out in full so that `omega` sees one atom per
product. For a candidate `(y, z)`, with `d = t * s - r * u` the orientation:

* `(y * s - r * z) * d` is positive exactly when `y / z` lies strictly beyond the loop candidate,
* `(t * z - y * u) * d` is positive exactly when it lies strictly beyond the extended candidate,
* `(m * z - y * n) * d` is the oriented scaled distance from the target to `y / z`.
-/

/-! ## The three algebraic identities -/

/--
The identity behind the bracket: `z` splits as a positive combination of the two denominators
whenever the candidate lies strictly inside.
-/
private theorem bracket_identity (r s t u y z : Int)
    (hd : t * s - r * u = 1 ∨ t * s - r * u = -1) :
    z = (t * z - y * u) * (t * s - r * u) * s + (y * s - r * z) * (t * s - r * u) * u := by
  grind

/-- Pivoting the candidate's distance against the loop candidate's. -/
private theorem loop_pivot (m n b r s t u y z : Int)
    (hres : (m * s - r * n) * (t * s - r * u) = b) :
    b * z - (m * z - y * n) * (t * s - r * u) * s
      = n * ((y * s - r * z) * (t * s - r * u)) := by
  grind

/-- Pivoting the candidate's distance against the extended candidate's. -/
private theorem extended_pivot (m n c r s t u y z : Int)
    (hres : (t * n - m * u) * (t * s - r * u) = c) :
    c * z + (m * z - y * n) * (t * s - r * u) * u
      = n * ((t * z - y * u) * (t * s - r * u)) := by
  grind

namespace Bracketing

variable {m n l b c r s t u y z : Int}

/-! ## The bracket -/

/--
The bracket lemma: a candidate strictly inside the bracket has denominator exceeding the limit.

Both `(t*z - y*u)*d` and `(y*s - r*z)*d` are then positive integers, so at least one, and `z`
is at least `s + u`.
-/
public theorem lt_of_inside (h : Bracketing m n l b c r s t u)
    (hloop : 0 < (y * s - r * z) * (t * s - r * u))
    (hextended : 0 < (t * z - y * u) * (t * s - r * u)) :
    l < z := by
  have hid := bracket_identity r s t u y z h.det
  have h1 := Int.le_mul_of_one_le_left (a := (t * z - y * u) * (t * s - r * u)) (b := s)
    (by have := h.s_pos; omega) (by omega)
  have h2 := Int.le_mul_of_one_le_left (a := (y * s - r * z) * (t * s - r * u)) (b := u)
    (by have := h.u_pos; omega) (by omega)
  have := h.l_lt_add
  omega

/-- Contrapositive: every candidate within the denominator limit lies on one side or the other. -/
public theorem outside (h : Bracketing m n l b c r s t u) (hzl : z ≤ l) :
    (y * s - r * z) * (t * s - r * u) ≤ 0 ∨ (t * z - y * u) * (t * s - r * u) ≤ 0 := by
  rcases (by omega : (y * s - r * z) * (t * s - r * u) ≤ 0 ∨
      0 < (y * s - r * z) * (t * s - r * u)) with hloop | hloop
  · exact .inl hloop
  rcases (by omega : (t * z - y * u) * (t * s - r * u) ≤ 0 ∨
      0 < (t * z - y * u) * (t * s - r * u)) with hextended | hextended
  · exact .inr hextended
  exact absurd (h.lt_of_inside hloop hextended) (by omega)

/-! ## The absolute values on the algorithm's side -/

/-- The loop candidate's scaled distance to the target is `b`. -/
public theorem abs_loop (h : Bracketing m n l b c r s t u) : (m * s - r * n).abs = b :=
  Int.abs_eq_of_mul_sign h.det h.b_nonneg h.loop_residual

/-- The extended candidate's scaled distance to the target is `c`. -/
public theorem abs_extended (h : Bracketing m n l b c r s t u) : (m * u - t * n).abs = c := by
  refine Int.abs_eq_of_mul_sign (d := -(t * s - r * u)) (by have := h.det; omega)
    (by have := h.c_pos; omega) ?_
  have := h.extended_residual
  grind

/-! ## Candidates outside the bracket are no closer -/

/--
A candidate on the loop candidate's side of the bracket is no closer to the target than the loop
candidate is.
-/
public theorem loop_le_of_side (h : Bracketing m n l b c r s t u)
    (hside : (y * s - r * z) * (t * s - r * u) ≤ 0) :
    b * z ≤ (m * z - y * n).abs * s := by
  have hpivot := loop_pivot m n b r s t u y z h.loop_residual
  have hnonpos : n * ((y * s - r * z) * (t * s - r * u)) ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos (by have := h.n_pos; omega) hside
  have habs := Int.mul_sign_mul_le_abs_mul (a := m * z - y * n) h.det
    (e := s) (by have := h.s_pos; omega)
  omega

/-- Likewise on the extended candidate's side. -/
public theorem extended_le_of_side (h : Bracketing m n l b c r s t u)
    (hside : (t * z - y * u) * (t * s - r * u) ≤ 0) :
    c * z ≤ (m * z - y * n).abs * u := by
  have hpivot := extended_pivot m n c r s t u y z h.extended_residual
  have hnonpos : n * ((t * z - y * u) * (t * s - r * u)) ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos (by have := h.n_pos; omega) hside
  have habs := Int.neg_mul_sign_mul_le_abs_mul (a := m * z - y * n) h.det
    (e := u) (by have := h.u_pos; omega)
  omega

/-! ## When a candidate is exactly as close, it is the same fraction -/

/--
Cancelling a nonzero multiplier and a unit orientation from a vanishing cross-product.
-/
private theorem eq_of_mul_pivot_eq_zero {n w d : Int} (hn : 0 < n) (hd : d = 1 ∨ d = -1)
    (hzero : n * (w * d) = 0) : w = 0 := by
  rcases Int.mul_eq_zero.mp hzero with h | h
  · omega
  · rcases hd with rfl | rfl <;> omega

/-- Equality in `loop_le_of_side` forces the candidate to equal the loop candidate as a value. -/
public theorem eq_of_loop_le (h : Bracketing m n l b c r s t u)
    (hside : (y * s - r * z) * (t * s - r * u) ≤ 0)
    (hle : (m * z - y * n).abs * s ≤ b * z) :
    y * s = r * z := by
  have hpivot := loop_pivot m n b r s t u y z h.loop_residual
  have hnonpos : n * ((y * s - r * z) * (t * s - r * u)) ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos (by have := h.n_pos; omega) hside
  have habs := Int.mul_sign_mul_le_abs_mul (a := m * z - y * n) h.det
    (e := s) (by have := h.s_pos; omega)
  -- The pivot's right-hand side is squeezed to zero from both sides.
  have := eq_of_mul_pivot_eq_zero h.n_pos h.det (w := y * s - r * z) (by omega)
  omega

/-- Equality in `extended_le_of_side`, likewise. -/
public theorem eq_of_extended_le (h : Bracketing m n l b c r s t u)
    (hside : (t * z - y * u) * (t * s - r * u) ≤ 0)
    (hle : (m * z - y * n).abs * u ≤ c * z) :
    t * z = y * u := by
  have hpivot := extended_pivot m n c r s t u y z h.extended_residual
  have hnonpos : n * ((t * z - y * u) * (t * s - r * u)) ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos (by have := h.n_pos; omega) hside
  have habs := Int.neg_mul_sign_mul_le_abs_mul (a := m * z - y * n) h.det
    (e := u) (by have := h.u_pos; omega)
  have := eq_of_mul_pivot_eq_zero h.n_pos h.det (w := t * z - y * u) (by omega)
  omega

/-! ## An equal value needs at least the same denominator -/

/--
A candidate equal to the loop candidate as a value has at least its denominator.

This is the bracket identity again, with one of its two terms killed by the hypothesis: `z`
collapses to a single multiple of `s`, and a positive multiple of a positive number is at least
one times it. So denominator-minimality comes from the *determinant*, exactly as the bracket
does, and needs nothing about divisibility — coprimality of the loop candidate would serve here
too, but only because it is itself a consequence of the determinant.
-/
public theorem s_le_of_loop_eq (h : Bracketing m n l b c r s t u) (hz : 0 < z)
    (hval : y * s = r * z) : s ≤ z := by
  have hid := bracket_identity r s t u y z h.det
  have hzero : (y * s - r * z) * (t * s - r * u) * u = 0 := by
    rw [show y * s - r * z = 0 from by omega]; grind
  have hs := h.s_pos
  have hcof : 1 ≤ (t * z - y * u) * (t * s - r * u) := by
    rcases (by omega : (t * z - y * u) * (t * s - r * u) ≤ 0
        ∨ 1 ≤ (t * z - y * u) * (t * s - r * u)) with hle | hge
    · have := Int.mul_le_mul_of_nonneg_right hle (show (0 : Int) ≤ s by omega)
      omega
    · exact hge
  have := Int.le_mul_of_one_le_left (a := (t * z - y * u) * (t * s - r * u)) (b := s)
    (by omega) hcof
  omega

/-- Symmetrically, against the extended candidate: the other term of the identity vanishes. -/
public theorem u_le_of_extended_eq (h : Bracketing m n l b c r s t u) (hz : 0 < z)
    (hval : t * z = y * u) : u ≤ z := by
  have hid := bracket_identity r s t u y z h.det
  have hzero : (t * z - y * u) * (t * s - r * u) * s = 0 := by
    rw [show t * z - y * u = 0 from by omega]; grind
  have hu := h.u_pos
  have hcof : 1 ≤ (y * s - r * z) * (t * s - r * u) := by
    rcases (by omega : (y * s - r * z) * (t * s - r * u) ≤ 0
        ∨ 1 ≤ (y * s - r * z) * (t * s - r * u)) with hle | hge
    · have := Int.mul_le_mul_of_nonneg_right hle (show (0 : Int) ≤ u by omega)
      omega
    · exact hge
  have := Int.le_mul_of_one_le_left (a := (y * s - r * z) * (t * s - r * u)) (b := u)
    (by omega) hcof
  omega

end Bracketing
