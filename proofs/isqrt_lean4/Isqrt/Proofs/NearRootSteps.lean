/-
The lifting lemma in the algorithm's bit-oriented form, plus the closing correction step — the
near-square-root machinery both top-level correctness proofs share.

`key_isqrt_lemma` (in `Isqrt.Proofs.KeyLemma`) lifts a near square root across a *general* suitable
scaler `M`; the algorithms use the *specific* power-of-two scaler `2^shifter` carried by a
`SizedProblem`. The scaler crossings `descend_n_eq`/`newtonLift_eq` recast the shift-form
`descend`/`newtonLift` in the multiplicative `Ma + ⌊n / 4Ma⌋` form, and `isNearSquareRoot_newtonLift`
feeds them to the key lemma to give the concrete lift both proofs run.
`isIntegerSquareRoot_of_isNearSquareRoot` is the closing step: a near square root of `n`, corrected
by a single comparison, is the integer square root of `n`.
-/

module

public import Isqrt.Proofs.SizedProblem
import Isqrt.Proofs.KeyLemma
import Isqrt.Proofs.SupportLemmas

/-! ## Scaler crossings: the power-of-two scaler in multiplicative form -/

/-- The scaler `M = 2^shifter`: the multiplicative form of a `SizedProblem`'s step shift, linking its
shift/bit-length world to the `isSuitableScaler` notion the key lemma reads. -/
private def scaler (p : SizedProblem) : Int := 2 ^ p.shifter

/-- For `M = 2^k`, `a·2^k + ⌊⌊ν / 2^(k+2)⌋ / a⌋ = Ma + ⌊ν / 4Ma⌋`. -/
private theorem key_isqrt_body_eq {ν a M : Int} {k : Nat}
    (hM : M = 2 ^ k) :
    a * 2 ^ k + ν / 2 ^ (k + 2) / a
      = M * a + ν / (4 * M * a) := by
  subst hM
  have h_pow : (2 : Int) ^ (k + 2) = 4 * 2 ^ k := by
    rw [Int.pow_add]; grind only
  rw [h_pow, Int.ediv_ediv_of_nonneg
      (Int.mul_nonneg (by omega) (Int.pow_nonneg (by omega)))]
  grind only

/-- The descended value in multiplicative form: `(p.descend hc).n = p.n / (4·scaler²)`. -/
private theorem descend_n_eq (p : SizedProblem) (hc : 0 < p.c) :
    (p.descend hc).n = p.n / (4 * scaler p ^ 2) := by
  show p.n >>> (2 * p.shifter + 2) = p.n / (4 * scaler p ^ 2)
  have hpow : (4 : Int) * scaler p ^ 2 = 2 ^ (2 * p.shifter + 2) := by
    show (4 : Int) * (2 ^ p.shifter) ^ 2 = 2 ^ (2 * p.shifter + 2)
    rw [Int.pow_add, ← Int.pow_mul]; grind only
  rw [Int.shiftRight_eq_ediv, hpow]

/-- `newtonLift` in multiplicative form: `p.newtonLift a = scaler·a + p.n / (4·scaler·a)`. -/
private theorem newtonLift_eq (p : SizedProblem) {a : Int} :
    p.newtonLift a = scaler p * a + p.n / (4 * scaler p * a) := by
  show (a <<< p.shifter) + (p.n >>> (p.shifter + 2)) / a
      = scaler p * a + p.n / (4 * scaler p * a)
  rw [Int.shiftLeft_eq, Int.shiftRight_eq_ediv]
  exact key_isqrt_body_eq rfl

/-! ## Lifting: the key lemma at the algorithm's power-of-two scaler -/

/-- The scaler `2^shifter` is suitable for `p.n`: `4·scaler⁴ = 2^(4·shifter+2) ≤ p.n`, the exponent
below `p.n.size`. -/
private theorem isSuitableScaler_scaler (p : SizedProblem) (hc : 0 < p.c) :
    isSuitableScaler p.n (scaler p) := by
  obtain ⟨hpos, hc_eq⟩ := p.hsize
  show 0 < (2 : Int) ^ ((p.c - 1) / 2) ∧ 4 * ((2 : Int) ^ ((p.c - 1) / 2)) ^ 4 ≤ p.n
  refine ⟨Int.pow_pos (by decide), ?_⟩
  have hbound : (2 : Nat) ^ (4 * ((p.c - 1) / 2) + 2) ≤ p.n.toNat := Nat.lt_size.mp (by omega)
  have hbound' : (2 : Int) ^ (4 * ((p.c - 1) / 2) + 2) ≤ p.n := by
    rw [← Int.toNat_of_nonneg (Int.le_of_lt hpos)]; exact_mod_cast hbound
  calc 4 * ((2 : Int) ^ ((p.c - 1) / 2)) ^ 4
      = 2 ^ (4 * ((p.c - 1) / 2) + 2) := by rw [Int.pow_add, ← Int.pow_mul]; grind only
    _ ≤ p.n := hbound'

/-- The Newton refinement step: a near square root of the descended problem lifts to one of `p`. -/
public theorem isNearSquareRoot_newtonLift {p : SizedProblem} (hc : 0 < p.c) {a : Int}
    (h : isNearSquareRoot (p.descend hc).n a) : isNearSquareRoot p.n (p.newtonLift a) := by
  rw [descend_n_eq p hc] at h
  rw [newtonLift_eq p]
  exact key_isqrt_lemma (isSuitableScaler_scaler p hc) h

/-! ## Correction: near square root to integer square root -/

/-- Turn a near square root into the integer square root: subtract one exactly when `n < a*a`. -/
public theorem isIntegerSquareRoot_of_isNearSquareRoot {a n : Int} (h : isNearSquareRoot n a) :
    isIntegerSquareRoot n (if n < a * a then a - 1 else a) := by
  obtain ⟨ha_pos, h_lo, h_hi⟩ := h
  by_cases h_lt : n < a * a
  · simp only [h_lt, ↓reduceIte]
    exact ⟨by omega, Int.le_of_lt h_lo, by grind only⟩
  · simp only [h_lt, ↓reduceIte]
    exact ⟨Int.le_of_lt ha_pos, Int.not_lt.mp h_lt, h_hi⟩
