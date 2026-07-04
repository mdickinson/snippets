/-
General `Int` / `Nat` facts missing from the core library, plus basic properties of `Nat.size`
(bit length), and a small `Except`-monad helper.
-/

module

public import Isqrt.Proofs.NatSize

public section

/-! ## Shift ↔ division -/

/-- Right shift for an int matches division by a power of two. -/
theorem Int.shiftRight_eq_ediv (n : Int) (k : Nat) : n >>> k = n / 2 ^ k := by
  rw [Int.shiftRight_eq_div_pow]
  norm_cast

/-! ## Nat.size -/

/-- Defining property, with inequalities inverted. -/
theorem Nat.lt_size {n k : Nat} : k < n.size ↔ 2 ^ k ≤ n := by
  have := Nat.size_le (n := n) (k := k); omega

/-- The size of `0` is `0`. -/
theorem Nat.size_zero : Nat.size 0 = 0 := by
  exact Nat.eq_zero_of_le_zero (Nat.size_le.mpr (by omega))

/-- `n.size` is positive iff `n` is positive. -/
theorem Nat.size_pos {n : Nat} : 0 < n.size ↔ 0 < n := by
  rw [Nat.lt_size]; omega

/-- Right shifting a natural number by its size yields zero. -/
theorem Nat.shiftRight_size_self {n : Nat} : n >>> n.size = 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.pow_pos (by decide))]
  rw [←Nat.size_le]; omega

/-- Right shifting a natural number by less than its size gives something positive. -/
theorem Nat.shiftRight_pos {n k : Nat} (hk : k < n.size) : 0 < n >>> k := by
  rw [Nat.lt_size] at hk
  rw [Nat.shiftRight_eq_div_pow, Nat.div_pos_iff]
  grind only [Nat.pow_pos]

/-- Shifting right reduces the size by the shift amount. -/
theorem Nat.size_shiftRight {n k : Nat} : (n >>> k).size  = n.size - k := by
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.le_antisymm
  · rw [Nat.size_le]
    apply Nat.div_lt_of_lt_mul
    rw [←Nat.pow_add, ←Nat.size_le]
    omega
  · rw [Nat.sub_le_iff_le_add, Nat.size_le, Nat.pow_add]
    apply Nat.lt_mul_of_div_lt _ (Nat.pow_pos (by decide))
    rw [← Nat.size_le]
    omega

/-- `Except.ok a >>= f = f a` (definitional). -/
theorem Except.ok_bind {ε α β : Type _} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

end
