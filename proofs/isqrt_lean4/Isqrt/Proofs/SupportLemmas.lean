/-
General `Int` / `Nat` facts missing from the core library, plus basic properties of `Nat.size`
(bit length), and a small `Except`-monad helper.
-/

module

public import Isqrt.Proofs.NatSize

/-! ## Shift ↔ division -/

/-- Right shift for an int matches division by a power of two. -/
public theorem Int.shiftRight_eq_ediv (n : Int) (k : Nat) : n >>> k = n / 2 ^ k := by
  grind only [Int.shiftRight_eq_div_pow]

/-! ## Nat.size -/

/-- Defining property, with inequalities inverted. -/
public theorem Nat.lt_size {n k : Nat} : k < n.size ↔ 2 ^ k ≤ n := by
  grind only [Nat.size_le (n := n) (k := k)]

/-- `n.size` is zero iff `n` is zero. -/
public theorem Nat.size_eq_zero {n : Nat} : n.size = 0 ↔ n = 0 := by
  grind only [Nat.size_le (n := n) (k := 0)]

/-- The size of zero is zero. -/
public theorem Nat.size_zero : (0 : Nat).size = 0 := Nat.size_eq_zero.mpr rfl

/-- `n.size` is positive iff `n` is positive. -/
public theorem Nat.size_pos {n : Nat} : 0 < n.size ↔ 0 < n := by
  grind only [Nat.lt_size]

/-- Shifting right reduces the size by the shift amount. -/
public theorem Nat.size_shiftRight {n k : Nat} : (n >>> k).size  = n.size - k := by
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.le_antisymm
  · rw [Nat.size_le]
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, ← Nat.size_le]
    omega
  · rw [Nat.sub_le_iff_le_add, Nat.size_le, Nat.pow_add]
    apply Nat.lt_mul_of_div_lt _ (Nat.pow_pos (by decide))
    rw [← Nat.size_le]
    omega

/-- Right shifting a natural number by its size yields zero. -/
public theorem Nat.shiftRight_size_self {n : Nat} : n >>> n.size = 0 := by
  rw [← Nat.size_eq_zero, Nat.size_shiftRight]; grind only

/-- Right shifting a natural number by less than its size gives something positive. -/
public theorem Nat.shiftRight_pos {n k : Nat} (hk : k < n.size) : 0 < n >>> k := by
  rw [← Nat.size_pos, Nat.size_shiftRight]; grind only

/-- Defining property of `Nat.size`, lifted to `Int` via `toNat`. -/
public theorem Int.size_le {n : Int} {k : Nat} : n.toNat.size ≤ k ↔ n < 2 ^ k := by
  grind only [Nat.size_le, Nat.size_zero]

/-- The same, with inequalities inverted. -/
public theorem Int.lt_size {n : Int} {k : Nat} : k < n.toNat.size ↔ 2 ^ k ≤ n := by
  grind only [Int.size_le (n := n) (k := k)]

/-- Size of a right-shifted integer. -/
public theorem Int.size_shiftRight {n : Int} {k : Nat} :
    (n >>> k).toNat.size = n.toNat.size - k := by
  rcases n with n | n
  · simp only [ofNat_eq_natCast, toNat_natCast]
    exact Nat.size_shiftRight
  · simp only [negSucc_shiftRight, toNat_negSucc, Nat.size_zero]
    omega

/-- A right-shift of an integer by less than its size is positive. -/
public theorem Int.shiftRight_pos {n : Int} {k : Nat} (hk : k < n.toNat.size) : 0 < n >>> k := by
  rcases n with n | n
  · rw [ofNat_eq_natCast]; norm_cast; grind only [Nat.shiftRight_pos]
  · grind only [toNat_negSucc, Nat.size_zero]

/-! ## Except.ok binding -/

/-- `Except.ok a >>= f = f a` (definitional). -/
public theorem Except.ok_bind {ε α β : Type _} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl
