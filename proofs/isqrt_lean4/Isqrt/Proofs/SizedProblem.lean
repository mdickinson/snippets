/-
The `SizedProblem` algebra: the instance both correctness proofs operate on (a value `n`, a level
`c`, and the invariant `isSizedAt n c`), and the operations they run — `descend` (one reduction
step), `newtonLift` (lift a near square root back up), and `subAt` (the depth-`d` subproblem the
loop climbs). All are phrased in the algorithm's shift/bit-length language; the crossings to the
key lemma's multiplicative `Ma + ⌊n / 4Ma⌋` form live at the bottom.
-/

module

public import Isqrt.Definitions.Specification
public import Isqrt.Proofs.SizeConditions
import Isqrt.Proofs.PythonTranslation
import Isqrt.Proofs.SupportLemmas

public section

/-- A *sized problem*: a value `n`, a recursion level `c`, and the size invariant `isSizedAt n c`
relating them. -/
@[ext] structure SizedProblem where
  /-- The value whose near square root is sought (at this recursion level). -/
  n : Int
  /-- The recursion level. -/
  c : Nat
  /-- The size invariant `isSizedAt n c` in bit-length form. -/
  hsize : isSizedAt n c

namespace SizedProblem

/-- The power bound `hasSizeCondition p.n p.c`, derived from the bit-length field `hsize`. -/
theorem hsc (p : SizedProblem) : hasSizeCondition p.n p.c :=
  hasSizeCondition_of_isSizedAt p.hsize

/-- The step shift amount `⌊(c-1)/2⌋`. -/
@[expose] def shifter (p : SizedProblem) : Nat := (p.c - 1) / 2

/-- The step scaler `M = 2^shifter`, the multiplicative form of the shift the key lemma reads. -/
@[expose] def scaler (p : SizedProblem) : Int := 2 ^ p.shifter

/-- One reduction step: `(n, c) ↦ (n >>> (2·shifter+2), ⌊c/2⌋)`, carrying the invariant to the
child. -/
@[expose] def descend (p : SizedProblem) (hc : 0 < p.c) : SizedProblem :=
  ⟨p.n >>> (2 * p.shifter + 2), p.c >>> 1, size_condition_step hc p.hsize⟩

/-- The Newton combine lifting a value `a` for the descended problem back to `p`:
`(a <<< shifter) + ⌊(n >>> shifter+2) / a⌋`. -/
@[expose] def newtonLift (p : SizedProblem) (a : Int) : Int :=
  (a <<< p.shifter) + (p.n >>> (p.shifter + 2)) / a

/-- The depth-`d` subproblem (`d ≤ p.c`): value `p.n >>> 2(c-d)` at level `d`, with the inherited
invariant. -/
@[expose] def subAt (p : SizedProblem) (d : Nat) (hhi : d ≤ p.c) : SizedProblem :=
  ⟨p.n >>> (2 * (p.c - d)), d, size_condition_at_depth hhi p.hsize⟩

/-- Descending the depth-`d` subproblem gives the depth-`⌊d/2⌋` one:
`descend (p.subAt d) = p.subAt ⌊d/2⌋`. -/
theorem descend_subAt {p : SizedProblem} {d : Nat} (hhi : d ≤ p.c) (hd_pos : 0 < d) :
    (p.subAt d hhi).descend hd_pos
      = p.subAt (d >>> 1) (Nat.le_trans (Nat.shiftRight_le d 1) hhi) := by
  apply SizedProblem.ext
  · show (p.n >>> (2 * (p.c - d))) >>> (2 * ((d - 1) / 2) + 2) = p.n >>> (2 * (p.c - d / 2))
    rw [← Int.shiftRight_add,
        show 2 * (p.c - d) + (2 * ((d - 1) / 2) + 2) = 2 * (p.c - d / 2) from by omega]
  · rfl

/-- The decoded loop body is the Newton lift of the depth-`d` subproblem: with child shift
`e = ⌊d/2⌋`, `(a <<< d-e-1) + ⌊(p.n >>> 2c-e-d+1) / a⌋ = (p.subAt d).newtonLift a`. -/
theorem subAt_body_eq {p : SizedProblem} {d e : Nat} {a : Int} (hhi : d ≤ p.c)
    (he : e = d >>> 1) (hd_pos : 0 < d) :
    a <<< (d - e - 1) + (p.n >>> (2 * p.c - e - d + 1)) / a
      = (p.subAt d hhi).newtonLift a := by
  -- `d >>> 1` is `d / 2`; restate the child shift so the arithmetic below reads the division.
  have he : e = d / 2 := he
  show a <<< (d - e - 1) + (p.n >>> (2 * p.c - e - d + 1)) / a
      = a <<< ((d - 1) / 2) + ((p.n >>> (2 * (p.c - d))) >>> ((d - 1) / 2 + 2)) / a
  rw [← Int.shiftRight_add,
      show d - e - 1 = (d - 1) / 2 from by omega,
      show 2 * p.c - e - d + 1 = 2 * (p.c - d) + ((d - 1) / 2 + 2) from by omega]

/-! ### Crossings to the key lemma's multiplicative form -/

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

/-- `4·(2^k)² = 2^(2k+2)`. -/
private theorem four_mul_two_pow_sq (k : Nat) :
    (4 : Int) * (2 ^ k) ^ 2 = 2 ^ (2 * k + 2) := by
  rw [Int.pow_add, ←Int.pow_mul]; grind only

/-- The descended value in multiplicative form: `(p.descend hc).n = p.n / (4·scaler²)`. -/
theorem descend_n_eq (p : SizedProblem) (hc : 0 < p.c) :
    (p.descend hc).n = p.n / (4 * p.scaler ^ 2) := by
  show p.n >>> (2 * p.shifter + 2) = p.n / (4 * p.scaler ^ 2)
  rw [Int.shiftRight_eq_ediv,
    show (4 : Int) * p.scaler ^ 2 = 2 ^ (2 * p.shifter + 2) from four_mul_two_pow_sq p.shifter]

/-- `newtonLift` in multiplicative form: `p.newtonLift a = scaler·a + p.n / (4·scaler·a)`. -/
theorem newtonLift_eq (p : SizedProblem) {a : Int} :
    p.newtonLift a = p.scaler * a + p.n / (4 * p.scaler * a) := by
  show (a <<< p.shifter) + (p.n >>> (p.shifter + 2)) / a
      = p.scaler * a + p.n / (4 * p.scaler * a)
  rw [Int.shiftLeft_eq, Int.shiftRight_eq_ediv]
  exact key_isqrt_body_eq rfl

end SizedProblem

end
