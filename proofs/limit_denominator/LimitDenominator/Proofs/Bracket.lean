module

public import LimitDenominator.Proofs.AfterLoop

/-!
The bracket, transcribing the informal proof's § "Proof overview".

Every candidate with a positive denominator lies strictly beyond exactly one of the two
candidates; that split is `cases`, and everything after it is done twice, once per side.

Three quantities recur below, for a candidate `(y, z)` and the orientation `v`:

* `(y * s - r * z) * v` is positive exactly when `y / z` lies strictly beyond the loop candidate,
* `(t * z - y * u) * v` is positive exactly when it lies strictly beyond the extended candidate,
* `(m * z - y * n) * v` is the oriented scaled distance from the target to `y / z`.

The argument runs on those oriented quantities throughout. `Int.abs_cancel` reaches the
specification's absolute values at the end of each side, and hands back each bound's equality
case alongside it, the two sharing a chain.
-/

/-! ## The two bracket identities -/

/--
The candidate's numerator splits along the two cross-products. Multiplying out the right-hand
side leaves `y * ((t * s - r * u) * v)`, which is `y` by `det`.
-/
private theorem numerator_identity (r s t u v y z : Int) (hdet : (t * s - r * u) * v = 1) :
    y = (t * z - y * u) * v * r + (y * s - r * z) * v * t := by
  grind

/-- Likewise the denominator, and this is the one that closes the bracket. -/
private theorem denominator_identity (r s t u v y z : Int) (hdet : (t * s - r * u) * v = 1) :
    z = (t * z - y * u) * v * s + (y * s - r * z) * v * u := by
  grind

/--
What the identities buy once one cross-product vanishes, the same either way round: a rival that is
a positive multiple of one denominator needs at least that denominator, and at exactly that
denominator the multiplier is `1`, which reads its numerator off too.
-/
private theorem le_of_eq_mul {A R S y z : Int} (hA : 0 < A) (hS : 0 < S)
    (hy : y = A * R) (hz : z = A * S) : S ≤ z ∧ (S = z → y = R) := by
  have := Int.le_mul_of_one_le_left (a := A) (b := S) (by omega) (by omega)
  refine ⟨by omega, fun hSz => ?_⟩
  rw [Int.eq_of_mul_eq_mul_right (show S ≠ 0 by omega) (show A * S = 1 * S by omega)] at hy
  omega

/-! ## The two pivot identities -/

/--
Pivoting the candidate's distance against the loop candidate's. Neither pivot needs `det`: they
are ring identities in an arbitrary `v`, given only the residual that defines `b` or `c`.
-/
private theorem loop_pivot (m n b r s v y z : Int) (hres : (m * s - r * n) * v = b) :
    b * z - (m * z - y * n) * v * s = n * ((y * s - r * z) * v) := by
  grind

/-- Pivoting the candidate's distance against the extended candidate's. -/
private theorem extended_pivot (m n c t u v y z : Int) (hres : (t * n - m * u) * v = c) :
    c * z + (m * z - y * n) * v * u = n * ((t * z - y * u) * v) := by
  grind

/-! ## From a pivot to the specification's absolute values -/

/--
The step the two sides share: a pivot identity with a nonpositive right-hand side, cancelled down
to absolute values.

Only the orientation `V` differs between them — `v` on the loop candidate's side, `-v` on the
extended candidate's — together with which cross-product plays `X`. The rival's own
`m * z - y * n` is the same `g` either way, and that is what lets one lemma serve both.
-/
private theorem abs_le_of_pivot {n x g V z S X : Int} (hn : 0 < n) (hV : V ≠ 0) (hz : 0 < z)
    (hS : 0 < S) (hnonneg : 0 ≤ x * V) (hX : X ≤ 0)
    (hpivot : x * V * z - g * V * S = n * X) :
    x.abs * z ≤ g.abs * S ∧ (g.abs * S ≤ x.abs * z → X = 0) := by
  have hnX : n * X ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hX
  obtain ⟨hle, heq⟩ := Int.abs_cancel (y := g) hV hz hS
    (Int.mul_nonneg hnonneg (by omega)) (by omega)
  exact ⟨hle, fun hrev => Int.eq_of_mul_eq_mul_left (show n ≠ 0 by omega)
    (show n * X = n * 0 by have := heq hrev; omega)⟩

namespace Bracketing

variable {m n l b c r s t u v y z : Int}

/-! ## The orientation is nonzero -/

/-- All the orientation is asked for beyond the identities: `v = 0` would make `det` read
`0 = 1`. -/
public theorem v_ne_zero (h : Bracketing m n l b c r s t u v) : v ≠ 0 := by
  have hdet := h.det
  intro h0
  rw [h0, Int.mul_zero] at hdet
  omega

/-- The extended candidate's residual, oriented the other way: `(m*u - t*n)(-v) = c`. -/
private theorem extended_residual_neg (h : Bracketing m n l b c r s t u v) :
    (m * u - t * n) * -v = c := by
  have := h.extended_residual; grind

/-! ## The bracket -/

/--
The bracket lemma: a candidate strictly beyond both — strictly inside the bracket — has
denominator exceeding the limit, both cross-products being positive integers and so at least
`1`.
-/
public theorem lt_of_inside (h : Bracketing m n l b c r s t u v)
    (hloop : 0 < (y * s - r * z) * v) (hextended : 0 < (t * z - y * u) * v) :
    l < z := by
  have hid := denominator_identity r s t u v y z h.det
  have h1 := Int.le_mul_of_one_le_left (a := (t * z - y * u) * v) (b := s)
    (by have := h.s_pos; omega) (by omega)
  have h2 := Int.le_mul_of_one_le_left (a := (y * s - r * z) * v) (b := u)
    (by have := h.u_pos; omega) (by omega)
  have := h.l_lt_add
  omega

/--
Dually, a candidate with a positive denominator lies strictly beyond at least one of the two:
were both cross-products nonpositive, the denominator identity would make `z` nonpositive too.
-/
private theorem lt_of_outside (h : Bracketing m n l b c r s t u v) (hz : 0 < z) :
    0 < (y * s - r * z) * v ∨ 0 < (t * z - y * u) * v := by
  rcases (by omega : 0 < (y * s - r * z) * v ∨ (y * s - r * z) * v ≤ 0) with hloop | hloop
  · exact .inl hloop
  rcases (by omega : 0 < (t * z - y * u) * v ∨ (t * z - y * u) * v ≤ 0) with hext | hext
  · exact .inr hext
  have hid := denominator_identity r s t u v y z h.det
  have h1 := Int.mul_le_mul_of_nonneg_right hext (show (0 : Int) ≤ s by have := h.s_pos; omega)
  have h2 := Int.mul_le_mul_of_nonneg_right hloop (show (0 : Int) ≤ u by have := h.u_pos; omega)
  omega

/--
The only case split in the rest of the argument: the candidate is on the loop candidate's side
of the bracket, or on the extended candidate's.
-/
public theorem cases (h : Bracketing m n l b c r s t u v) (hz : 0 < z) (hzl : z ≤ l) :
    ((y * s - r * z) * v ≤ 0 ∧ 0 < (t * z - y * u) * v)
      ∨ (0 < (y * s - r * z) * v ∧ (t * z - y * u) * v ≤ 0) := by
  rcases (by omega : (t * z - y * u) * v ≤ 0 ∨ 0 < (t * z - y * u) * v) with hext | hext
  · exact .inr ⟨(h.lt_of_outside hz).resolve_right (by omega), hext⟩
  refine .inl ⟨?_, hext⟩
  rcases (by omega : (y * s - r * z) * v ≤ 0 ∨ 0 < (y * s - r * z) * v) with hloop | hloop
  · exact hloop
  exact absurd (h.lt_of_inside hloop hext) (by omega)

/-! ## The loop candidate's side -/

/--
On the loop candidate's side, the loop candidate is at least as close; and a rival matching
that bound squeezes the loop pivot's right-hand side to zero, so the cross-product vanishes.
-/
public theorem loop_le_of_loop_side (h : Bracketing m n l b c r s t u v) (hz : 0 < z)
    (hside : (y * s - r * z) * v ≤ 0) :
    (m * s - r * n).abs * z ≤ (m * z - y * n).abs * s
      ∧ ((m * z - y * n).abs * s ≤ (m * s - r * n).abs * z → (y * s - r * z) * v = 0) :=
  abs_le_of_pivot h.n_pos h.v_ne_zero hz h.s_pos
    (by rw [h.loop_residual]; exact h.b_nonneg) hside
    (by rw [h.loop_residual]; exact loop_pivot m n b r s v y z h.loop_residual)

/-! ## The extended candidate's side -/

/--
Symmetrically on the extended candidate's side, cancelling the orientation `-v` — the one that
makes *that* candidate's residual nonnegative.
-/
public theorem extended_le_of_extended_side (h : Bracketing m n l b c r s t u v) (hz : 0 < z)
    (hside : (t * z - y * u) * v ≤ 0) :
    (m * u - t * n).abs * z ≤ (m * z - y * n).abs * u
      ∧ ((m * z - y * n).abs * u ≤ (m * u - t * n).abs * z → (t * z - y * u) * v = 0) :=
  abs_le_of_pivot (V := -v) h.n_pos (by have := h.v_ne_zero; omega) hz h.u_pos
    (by rw [h.extended_residual_neg]; have := h.c_pos; omega) hside
    (by rw [h.extended_residual_neg]
        have := extended_pivot m n c t u v y z h.extended_residual
        grind)

/-! ## Across the comparison -/

/--
On the extended candidate's side the *loop* candidate is still at least as close, provided it is
the nearer. The chain is the extended pivot scaled by `s` and the comparison scaled by `z`,
leaving a common `u` to cancel alongside the orientation; a rival matching it makes both steps
equalities, which is why the equality case also pins the comparison to an exact tie.
-/
public theorem loop_le_of_extended_side (h : Bracketing m n l b c r s t u v) (hz : 0 < z)
    (hside : (t * z - y * u) * v ≤ 0) (hnearer : b * u ≤ c * s) :
    (m * s - r * n).abs * z ≤ (m * z - y * n).abs * s
      ∧ ((m * z - y * n).abs * s ≤ (m * s - r * n).abs * z →
          b * u = c * s ∧ (t * z - y * u) * v = 0) := by
  have hs := h.s_pos
  have hu := h.u_pos
  have huz : (0 : Int) < u * z := Int.mul_pos hu hz
  have hus : (0 : Int) < u * s := Int.mul_pos hu hs
  have hpivot := extended_pivot m n c t u v y z h.extended_residual
  have hnonpos : n * ((t * z - y * u) * v) ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos (by have := h.n_pos; omega) hside
  have h21 : c * z * s ≤ -((m * z - y * n) * v * u) * s :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  have h22 : b * u * z ≤ c * s * z := Int.mul_le_mul_of_nonneg_right hnearer (by omega)
  obtain ⟨hle, heq⟩ := Int.abs_cancel (x := m * s - r * n) (y := -(m * z - y * n))
    h.v_ne_zero huz hus
    (by rw [h.loop_residual]; exact Int.mul_nonneg h.b_nonneg (by omega))
    (by rw [h.loop_residual]; grind)
  rw [Int.abs_neg] at hle heq
  refine ⟨Int.le_of_mul_le_mul_left (by grind) hu, fun hrev => ?_⟩
  have hscaled := Int.mul_le_mul_of_nonneg_left hrev (show (0 : Int) ≤ u by omega)
  have hchain := heq (by grind)
  rw [h.loop_residual] at hchain
  -- Both ends of the chain in one orientation, so that `omega` can squeeze the two steps.
  have e1 : b * u * z = -((m * z - y * n) * v * u) * s := by grind
  have e2 : c * z * s = c * s * z := by grind
  have htie : b * u * z = c * s * z := by omega
  have h3 : c * z = -((m * z - y * n) * v * u) :=
    Int.eq_of_mul_eq_mul_right (show s ≠ 0 by omega) (by omega)
  exact ⟨Int.eq_of_mul_eq_mul_right (show z ≠ 0 by omega) htie,
    Int.eq_of_mul_eq_mul_left (show n ≠ 0 by have := h.n_pos; omega)
      (show n * ((t * z - y * u) * v) = n * 0 by omega)⟩

/--
And on the loop candidate's side the *extended* candidate is strictly closer when the comparison
is strict. Strictness makes this subcase's tie-break clauses vacuous, so there is no equality
case to return.
-/
public theorem extended_lt_of_loop_side (h : Bracketing m n l b c r s t u v) (hz : 0 < z)
    (hside : (y * s - r * z) * v ≤ 0) (hnearer : c * s < b * u) :
    (m * u - t * n).abs * z < (m * z - y * n).abs * u := by
  have hs := h.s_pos
  have hu := h.u_pos
  have hsz : (0 : Int) < s * z := Int.mul_pos hs hz
  have hsu : (0 : Int) < s * u := Int.mul_pos hs hu
  have hpivot := loop_pivot m n b r s v y z h.loop_residual
  have hnonpos : n * ((y * s - r * z) * v) ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos (by have := h.n_pos; omega) hside
  -- The loop pivot scaled by `u`, and the strict comparison scaled by `z`.
  have h30 : b * z * u ≤ (m * z - y * n) * v * s * u :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  have h31 : c * s * z < b * u * z := Int.mul_lt_mul_of_pos_right hnearer hz
  have hkey := Int.abs_lt_abs_of_mul_lt_mul (x := m * u - t * n) (y := -(m * z - y * n)) (v := -v)
    (by have := h.v_ne_zero; omega) hsz hsu
    (by rw [h.extended_residual_neg]; exact Int.mul_nonneg (by have := h.c_pos; omega) (by omega))
    (by rw [h.extended_residual_neg]; grind)
  rw [Int.abs_neg] at hkey
  exact Int.lt_of_mul_lt_mul_left (a := s) (by grind) (by omega)

/-! ## What a vanishing cross-product buys -/

/--
A vanishing loop cross-product collapses both identities onto the loop candidate's `r` and `s`.

So denominator-minimality comes from the *determinant*, not from any divisibility argument.
-/
public theorem s_le_of_loop_vanishes (h : Bracketing m n l b c r s t u v)
    (hextended : 0 < (t * z - y * u) * v) (hzero : (y * s - r * z) * v = 0) :
    s ≤ z ∧ (s = z → y = r) := by
  have hid := denominator_identity r s t u v y z h.det
  have hnum := numerator_identity r s t u v y z h.det
  rw [hzero] at hid hnum
  exact le_of_eq_mul hextended h.s_pos (by omega) (by omega)

/--
Symmetrically for a vanishing extended cross-product.
-/
public theorem u_le_of_extended_vanishes (h : Bracketing m n l b c r s t u v)
    (hloop : 0 < (y * s - r * z) * v) (hzero : (t * z - y * u) * v = 0) :
    u ≤ z ∧ (u = z → y = t) := by
  have hid := denominator_identity r s t u v y z h.det
  have hnum := numerator_identity r s t u v y z h.det
  rw [hzero] at hid hnum
  exact le_of_eq_mul hloop h.u_pos (by omega) (by omega)

end Bracketing
