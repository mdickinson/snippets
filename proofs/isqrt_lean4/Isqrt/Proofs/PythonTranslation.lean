/-
The bit-level theory the correctness proofs consume, all stated in pure Euclidean division `· / ·`
(`Int.ediv`) / `2 ^ ·` form (no Python operators) so the proofs build on them directly. Three
groups. (The pure-integer mathematics — near-square-root theory and the Newton-step key lemma —
lives in `Isqrt.Proofs.KeyLemma`.)

**Value extraction.** For a positive divisor `pyFloordiv` returns `.ok (a / b)` — its `Int.fdiv`
agrees with `Int.ediv` there, so the bridge hands the proofs the `· / ·` form core's library is
richest in — and `pyLshift` / `pyRshift` return `.ok` of the native shift `· <<< ·` / `· >>> ·`. The
`_eq_ok` lemmas are the bridges the proofs use to step through the `do`-block
once the side conditions (positive divisor, nonneg shift) are discharged; the shift forms keep the
proofs in shift vocabulary until the key-lemma seam.

**Bit length.** The power-of-two facts about `int.bit_length()`. The public `Int.bitLength` is the
Python `bit_length()` model; these lemmas connect it, via `Nat.log2`, to the power-of-two bounds
the size-condition and loop-depth proofs consume — with the `n = 0` guard discharged at the seam,
since each consumer applies them to a positive argument.

**Scaler encoding.** The shift exponents the algorithm divides by are the key lemma's
`4M²` / `4Ma` denominators for the scaler `M = 2^k`: `four_mul_two_pow_sq` and
`key_isqrt_body_eq` are the bridges that let both correctness proofs read a shift as
division by the scaler.
-/

module

public import Isqrt.Definitions.PythonPrimitives
public import Isqrt.Proofs.SupportLemmas

/-- `pyFloordiv` doesn't raise, and returns the Euclidean quotient, for a positive divisor. -/
public theorem pyFloordiv_eq_ok {a b : Int} (hb : 0 < b) :
    pyFloordiv a b = .ok (a / b) := by
  unfold pyFloordiv; split
  · omega
  · rw [Int.fdiv_eq_ediv_of_nonneg a (Int.le_of_lt hb)]; rfl

/-- `pyLshift` corresponds to <<< and doesn't raise for a nonnegative shift. -/
public theorem pyLshift_eq_ok {n k : Int} (hk : 0 ≤ k) :
    pyLshift n k = .ok (n <<< k.toNat) := by
  unfold pyLshift; split
  · omega
  · rfl

/-- `pyRshift` corresponds to >>> and doesn't raise for a nonnegative shift. -/
public theorem pyRshift_eq_ok {n k : Int} (hk : 0 ≤ k) :
    pyRshift n k = .ok (n >>> k.toNat) := by
  unfold pyRshift; split
  · omega
  · rfl

/-- For nonnegative `m`, `bitLength` can be rewritten in terms of `m.toNat.size`. -/
public theorem Int.bitLength_eq {m : Int} (hm : 0 ≤ m) : m.bitLength = ↑m.toNat.size := by
  unfold Int.bitLength
  rw [show m.natAbs = m.toNat from by omega]
  rcases Int.lt_or_eq_of_le hm with hlt | rfl
  · rw [if_neg (by omega)]; norm_cast
    apply Nat.le_antisymm
    · apply Nat.succ_le_of_lt
      rw [Nat.log2_lt (by omega), ←Nat.size_spec]; omega
    · rw [Nat.size_spec, ←Nat.log2_lt (by omega)]; omega
  · rw [if_pos (by omega), toNat_zero, Nat.size_zero, cast_ofNat_Int]
