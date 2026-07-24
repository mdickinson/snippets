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

/-- Descent for an input `n` to the smaller `n` that we'll solve recursively. -/
public abbrev descend (n : Int) (k : Nat) : Int := n >>> (2 * k + 2)

/-- Lift of the solution for the descended `n` to the current `n`. -/
public abbrev newtonLift (n : Int) (k : Nat) (a : Int) : Int :=
  (a <<< k) + (n >>> (k + 2)) / a

/--
Key lemma in bitwise form.

For n ≥ 4, descending, solving the descended problem, and lifting the result
gives a solution to the original problem.
-/
public theorem nsqrt_lift {n : Int} (hn : 4 ≤ n) {a : Int}:
    let k := (n.toNat.size - 3) / 4
    isNearSquareRoot (descend n k) a → isNearSquareRoot n (newtonLift n k a) := by
  intro k

  /- Show that M := 2^k is a suitable scaler for n. -/
  let M : Int := 2^k
  have M_suitable : 4 * M^4 ≤ n := by
    rw [show 4 * M^4 = (2 : Int)^(4*k+2) by rw [← Int.pow_mul]; grind only]
    rw [← Int.lt_size]
    have : 2 < n.toNat.size := Int.lt_size.mpr (by omega)
    omega

  /- Rewrite the conclusion to match the original form of the key lemma. -/
  rw [newtonLift, descend]
  rw [Int.shiftRight_eq_ediv, Int.shiftRight_eq_ediv, Int.shiftLeft_eq, Int.mul_comm a]
  rw [Int.ediv_ediv_of_nonneg (Int.pow_nonneg (by decide))]
  rw [show (2 : Int)^(2 * k + 2) = 4 * M^2 by rw [← Int.pow_mul]; grind only]
  rw [show (2 : Int)^(k + 2) = 4 * M by grind only]
  rw [show (2 : Int)^k = M by rfl]

  /- Apply the key lemma. -/
  exact key_lemma ⟨Int.pow_pos (by decide), M_suitable⟩

/-- For `0 < n < 4`, `1` is a near square root of `n` — the recursion's base case. -/
public theorem nsqrt_base {n : Int} (hn : 0 < n) (hn4 : n < 4) :
    isNearSquareRoot n 1 := by
  unfold isNearSquareRoot; omega
