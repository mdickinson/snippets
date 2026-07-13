/-
`Nat.size` (bit length) and its defining property `Nat.size_le`.
-/

module

/-- Minimum number of bits required to represent a natural number. -/
public def Nat.size (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

/-- Defining property of `Nat.size`: `n.size ≤ k ↔ n < 2^k`. -/
public theorem Nat.size_le {n k : Nat} : n.size ≤ k ↔ n < 2 ^ k := by
  unfold Nat.size
  cases n with
  | zero => rw [if_pos rfl]; grind only [Nat.pow_pos, Nat.zero_le k]
  | succ => rw [if_neg (by omega)]; grind only [Nat.log2_lt]
