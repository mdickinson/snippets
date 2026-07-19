/-
Bridges from the Python primitives to the pure `Int` / `Nat` forms the correctness
proofs reason with.
-/

module

public import Isqrt.Definitions.PythonPrimitives
public import Isqrt.Proofs.NatSize
public import Isqrt.Proofs.SupportLemmas

/-- For a positive divisor, `pyFloordiv a b` returns `.ok (a / b)`. -/
public theorem pyFloordiv_ok_bind {α : Type} {a b : Int} (hb : 0 < b) (f : Int → PyExcept α) :
    (pyFloordiv a b >>= f) = f (a / b) := by
  rw [pyFloordiv, if_neg (by omega), Int.fdiv_eq_ediv_of_nonneg _ (by omega)]; rfl

/-- For a nonnegative shift, `pyLshift n k` returns `.ok (n <<< k.toNat)`. -/
public theorem pyLshift_ok_bind {α : Type} {n : Int} {k : Nat} (f : Int → PyExcept α) :
    (pyLshift n ↑k >>= f) = f (n <<< k) := by
  rw [pyLshift, if_neg (by omega)]; rfl

/-- For a nonnegative shift, `pyRshift n k` returns `.ok (n >>> k.toNat)`. -/
public theorem pyRshift_ok_bind {α : Type} {n : Int} {k : Nat} (f : Int → PyExcept α) :
    (pyRshift n ↑k >>= f) = f (n >>> k) := by
  rw [pyRshift, if_neg (by omega)]; rfl

/-- For a Nat `m`, `bitLength` and `size` match. -/
public theorem Nat.bitLength_eq (m : Nat) : (m : Int).bitLength = m.size := by
  unfold Int.bitLength; rcases m.eq_zero_or_pos with rfl | hm_pos
  · rw [if_pos (by rfl), Nat.size_zero]; rfl
  · rw [if_neg (by omega)]; norm_cast
    show m.log2 + 1 = m.size
    apply Nat.le_antisymm
    · apply Nat.succ_le_of_lt; rw [Nat.log2_lt (by omega), ← Nat.size_le]; omega
    · rw [Nat.size_le, ← Nat.log2_lt (by omega)]; omega

/-- For a nonnegative Int `m`, `bitLength` and `size` match. -/
public theorem Int.bitLength_eq {m : Int} (hm : 0 ≤ m) : m.bitLength = ↑m.toNat.size :=
  (Int.toNat_of_nonneg hm) ▸ Nat.bitLength_eq m.toNat
