/- Key lemma in bitwise form.

Restatement of the lemma in `KeyLemma.lean` for a specific scaler `M`, equal to
the largest power of two that gives a suitable scaler for `n`.  Multiplications
and divisions by powers of two are expressed as bit shifts in the restated lemma.

Informally, writing `n.size` for the bit length of `n`: if `M = 2^k` for some
`k ≥ 0`, then `M` is a suitable scaler for `n` when

- 4M⁴ ≤ n, i.e.
- 2^(4k+2) ≤ n, which is equivalent to
- 4k + 2 < n.size, which is equivalent to
- k ≤ (n.size - 3) / 4.

So the largest power-of-two suitable scaler is 2^((n.size - 3) / 4).
-/

module

public import Isqrt.Definitions.Specification
public import Isqrt.Proofs.NatSize
import Isqrt.Proofs.KeyLemma
import Isqrt.Proofs.SupportLemmas

/--
Given `4 ≤ n`, let `k = (n.size - 3) / 4`, where `n.size` is the bit length of `n`.

Then if `a` is a near square root of `n >>> (2 * k + 2)`,
`(a <<< k) + (n >>> (k + 2)) / a` is a near square root of `n`.
-/
public theorem key_lemma_bitwise {n : Int} (hn : 4 ≤ n) {a : Int}:
    let k := (n.toNat.size - 3) / 4
    isNearSquareRoot (n >>> (2 * k + 2)) a →
    isNearSquareRoot n ((a <<< k) + (n >>> (k + 2)) / a) := by
  intro k

  /- Rewrite the conclusion to match the original form of the key lemma. -/
  rw [Int.shiftRight_eq_ediv, Int.shiftRight_eq_ediv, Int.shiftLeft_eq, Int.mul_comm a]
  rw [Int.ediv_ediv_of_nonneg (Int.pow_nonneg (by decide))]
  rw [show (2 : Int)^(2 * k + 2) = 4 * (2^k)^2 by rw [← Int.pow_mul]; grind only]
  rw [show (2 : Int)^(k + 2) = 4 * 2^k by grind only]

  /- Apply the key lemma with M := 2^k. -/
  apply key_lemma (M := 2^k)

  /- Show that 2^k is a suitable scaler for n. -/
  refine ⟨Int.pow_pos (by decide), ?_⟩
  rw [show 4 * (2^k)^4 = (2 : Int)^(4*k+2) by rw [← Int.pow_mul]; grind only]
  rw [← Int.toNat_of_nonneg (by omega : 0 ≤ n)]; norm_cast
  rw [← Nat.lt_size]
  have : 2 < n.toNat.size := Nat.lt_size.mpr (by omega)
  omega
