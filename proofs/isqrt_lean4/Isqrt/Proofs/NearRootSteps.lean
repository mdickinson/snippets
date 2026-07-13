/-
The near-square-root steps both correctness proofs assemble: the base case `isNearSquareRoot_one`
(level zero ⇒ `1`), the Newton step `isNearSquareRoot_newtonLift`, and the closing correction
`isIntegerSquareRoot_of_isNearSquareRoot`. The step recasts the shift-form `descend`/`newtonLift`
into the multiplicative form the general key lemma reads.
-/

module

public import Isqrt.Definitions.Specification
public import Isqrt.Proofs.SizedProblem
import Isqrt.Proofs.KeyLemma
import Isqrt.Proofs.NatSize
import Isqrt.Proofs.SupportLemmas

/-! ## The power-of-two scaler -/

/-- The scaler `M = 2^shifter`: the multiplicative form of a `SizedProblem`'s step shift, linking its
shift/bit-length world to the `isSuitableScaler` notion the key lemma reads. -/
private def scaler (p : SizedProblem) : Int := 2 ^ p.shifter

/-- For `M = 2^k`, `a·2^k + ⌊⌊ν / 2^(k+2)⌋ / a⌋ = Ma + ⌊ν / 4Ma⌋`. -/
private theorem key_isqrt_body_eq {ν M a : Int} {k : Nat}
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
private theorem descend_n_mul (p : SizedProblem) (hc : 0 < p.c) :
    (p.descend hc).n = p.n / (4 * scaler p ^ 2) := by
  rw [SizedProblem.descend_n]
  have hpow : (4 : Int) * scaler p ^ 2 = 2 ^ (2 * p.shifter + 2) := by
    show (4 : Int) * (2 ^ p.shifter) ^ 2 = 2 ^ (2 * p.shifter + 2)
    rw [Int.pow_add, ← Int.pow_mul]; grind only
  rw [Int.shiftRight_eq_ediv, hpow]

/-- `newtonLift` in multiplicative form: `p.newtonLift a = scaler·a + p.n / (4·scaler·a)`. -/
private theorem newtonLift_mul (p : SizedProblem) {a : Int} :
    p.newtonLift a = scaler p * a + p.n / (4 * scaler p * a) := by
  rw [SizedProblem.newtonLift_eq, Int.shiftLeft_eq, Int.shiftRight_eq_ediv]
  exact key_isqrt_body_eq rfl

/-- The scaler `2^shifter` is suitable for `p.n`: `4·scaler⁴ = 2^(4·shifter+2) ≤ p.n`, the exponent
below `p.n.size`. -/
private theorem isSuitableScaler_scaler (p : SizedProblem) (hc : 0 < p.c) :
    isSuitableScaler p.n (scaler p) := by
  obtain ⟨hpos, hc_eq⟩ := p.hsize
  simp only [scaler, SizedProblem.shifter_eq]
  show 0 < (2 : Int) ^ ((p.c - 1) / 2) ∧ 4 * ((2 : Int) ^ ((p.c - 1) / 2)) ^ 4 ≤ p.n
  refine ⟨Int.pow_pos (by decide), ?_⟩
  have hbound : (2 : Nat) ^ (4 * ((p.c - 1) / 2) + 2) ≤ p.n.toNat := Nat.lt_size.mp (by omega)
  have hbound' : (2 : Int) ^ (4 * ((p.c - 1) / 2) + 2) ≤ p.n := by
    rw [← Int.toNat_of_nonneg (Int.le_of_lt hpos)]; exact_mod_cast hbound
  calc 4 * ((2 : Int) ^ ((p.c - 1) / 2)) ^ 4
      = 2 ^ (4 * ((p.c - 1) / 2) + 2) := by rw [Int.pow_add, ← Int.pow_mul]; grind only
    _ ≤ p.n := hbound'

/-! ## Base case, Newton lift, correction -/

/-- Base case: at level `p.c = 0` the value `p.n` is below 4, so `1` is a near square root of it. -/
public theorem isNearSquareRoot_one (p : SizedProblem) (hc : p.c = 0) :
    isNearSquareRoot p.n 1 := by
  obtain ⟨hpos, hc_eq⟩ := p.hsize
  have hlt : p.n.toNat < 4 := by simpa using Nat.size_le.mp (show p.n.toNat.size ≤ 2 by omega)
  exact ⟨Int.one_pos, by show (1 - 1) * (1 - 1) < p.n; omega, by show p.n < (1 + 1) * (1 + 1); omega⟩

/-- The Newton refinement step: a near square root of the descended problem lifts to one of `p`. -/
public theorem isNearSquareRoot_newtonLift (p : SizedProblem) (hc : 0 < p.c) {a : Int}
    (h : isNearSquareRoot (p.descend hc).n a) : isNearSquareRoot p.n (p.newtonLift a) := by
  rw [descend_n_mul p hc] at h
  rw [newtonLift_mul p]
  exact key_lemma (isSuitableScaler_scaler p hc) h

/-- Turn a near square root into the integer square root: subtract one exactly when `n < a*a`. -/
public theorem isIntegerSquareRoot_of_isNearSquareRoot {n a : Int} (h : isNearSquareRoot n a) :
    isIntegerSquareRoot n (if n < a * a then a - 1 else a) := by
  obtain ⟨ha_pos, h_lo, h_hi⟩ := h
  by_cases h_lt : n < a * a
  · simp only [h_lt, ↓reduceIte]
    exact ⟨by omega, Int.le_of_lt h_lo, by grind only⟩
  · simp only [h_lt, ↓reduceIte]
    exact ⟨Int.le_of_lt ha_pos, Int.not_lt.mp h_lt, h_hi⟩
