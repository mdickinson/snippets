/-
Bridges from the Python primitives to the pure `Int` / `Nat` forms the correctness proofs reason
with: the `_eq_ok` lemmas that discharge each operation's error branch and expose its value, and
`Int.bitLength_eq` relating `int.bit_length()` to `Nat.size`.
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
public theorem pyLshift_ok_bind {α : Type} {n k : Int} (hk : 0 ≤ k) (f : Int → PyExcept α) :
    (pyLshift n k >>= f) = f (n <<< k.toNat) := by
  rw [pyLshift, if_neg (by omega)]; rfl

/-- For a nonnegative shift, `pyRshift n k` returns `.ok (n >>> k.toNat)`. -/
public theorem pyRshift_ok_bind {α : Type} {n k : Int} (hk : 0 ≤ k) (f : Int → PyExcept α) :
    (pyRshift n k >>= f) = f (n >>> k.toNat) := by
  rw [pyRshift, if_neg (by omega)]; rfl

/-- For nonnegative `m`, `m.bitLength = ↑m.toNat.size`. -/
public theorem Int.bitLength_eq {m : Int} (hm : 0 ≤ m) : m.bitLength = ↑m.toNat.size := by
  unfold Int.bitLength
  rw [show m.natAbs = m.toNat from by omega]
  rcases Int.lt_or_eq_of_le hm with hlt | rfl
  · rw [if_neg (by omega)]; norm_cast
    apply Nat.le_antisymm
    · apply Nat.succ_le_of_lt; rw [Nat.log2_lt (by omega), ← Nat.size_le]; omega
    · rw [Nat.size_le, ← Nat.log2_lt (by omega)]; omega
  · rw [if_pos rfl]; norm_cast
    exact Nat.size_zero.symm
