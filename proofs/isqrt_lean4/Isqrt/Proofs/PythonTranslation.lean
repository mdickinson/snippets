/-
Bridges from the Python primitives to the pure `Int` / `Nat` forms the correctness
proofs reason with.
-/

module

public import Isqrt.Definitions.PythonPrimitives
public import Isqrt.Proofs.NatSize
public import Isqrt.Proofs.SupportLemmas

open scoped Python

/-- For a positive divisor, `a // b` returns `.ok (a / b)`. -/
public theorem pyFloordiv_ok_bind {α : Type} {a b : Int} (hb : 0 < b) (f : Int → PyExcept α) :
    (a // b >>= f) = f (a / b) := by
  rw [pyFloordiv, if_neg (by omega), Int.fdiv_eq_ediv_of_nonneg _ (by omega)]; rfl

/-- For a nonnegative shift, `n << k` returns `.ok (n <<< k.toNat)`. -/
public theorem pyLshift_ok_bind {α : Type} {n : Int} {k : Nat} (f : Int → PyExcept α) :
    (n << ↑k >>= f) = f (n <<< k) := by
  rw [pyLshift, if_neg (by omega)]; rfl

/-- For a nonnegative shift, `n >> k` returns `.ok (n >>> k.toNat)`. -/
public theorem pyRshift_ok_bind {α : Type} {n : Int} {k : Nat} (f : Int → PyExcept α) :
    (n >> ↑k >>= f) = f (n >>> k) := by
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

/--
Translation used by both the recursive and iterative correctness proofs.
-/
public theorem half_dec_bitLength {α : Type} {n : Int} (hpos : 0 < n) (f : Int -> PyExcept α):
    ((n.bitLength - 1) // 2) >>= f = f ((n.toNat.size - 1) / 2 : Nat) := by
  have hsize : 0 < n.toNat.size := Nat.size_pos.mpr (by omega)
  grind only [Int.bitLength_eq, pyFloordiv_ok_bind]

/-! ## Looping over a reversed range -/

/-- range of a casted Nat -/
theorem Nat.range_eq (n : Nat) : (range (n : Int)) = (List.range n).map Nat.cast := rfl

/-- The reverse range of 0 is empty.-/
theorem reverse_range_zero : (range (0 : Nat)).reverse = [] := by
  rw [Nat.range_eq, List.range_zero, List.map_nil, List.reverse_nil]

/-- The reverse range of a successor, as a cons. -/
theorem reverse_range_succ (n : Nat) : (range ↑(n + 1)).reverse = ↑n :: (range ↑n).reverse := by
  rw [Nat.range_eq, Nat.range_eq, List.range_succ, List.map_append, List.reverse_append]
  rfl

/--
Threading an invariant through a for loop over a reversed range, in a situation where
the loop body gives a pure yield (under the assumption of the invariant).
-/
public theorem forIn_reverse_range_invariant
    {m : Type -> Type} {α : Type} [Monad m] [LawfulMonad m]
    (n : Nat)
    (init : α)
    (step : α -> Nat -> α)
    (body : Int -> α -> m (ForInStep α))
    (invariant : α -> Nat -> Prop)
    (hinit : invariant init n)
    (hstep : ∀ {s : Nat}, s < n → ∀ r : α, invariant r (s + 1) →
      body ↑s r = pure (ForInStep.yield (step r s)) ∧ invariant (step r s) s) :
    ∃ y : α,
      (∀ g : α → m Int, forIn (range n).reverse init body >>= g = g y)
      ∧
      invariant y 0 := by
  induction n generalizing init with
  | zero => rw [reverse_range_zero, List.forIn_nil]; exact ⟨init, fun g => by rw [pure_bind], hinit⟩
  | succ n ind_hyp =>
    rw [reverse_range_succ, List.forIn_cons, (hstep (by omega) init hinit).1, pure_bind]
    exact ind_hyp (step init n) (hstep (by omega) init hinit).2 (fun hs => hstep (by omega))
