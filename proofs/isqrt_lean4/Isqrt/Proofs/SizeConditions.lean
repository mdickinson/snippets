/-
The bit-length size condition `isSizedAt` (`0 < n ∧ c = (n.toNat.size - 1)/2`, the algorithm's
seed), its descent, and the base case, all read off `Nat.size`.
-/

module

public import Isqrt.Definitions.Specification
public import Isqrt.Proofs.SupportLemmas

public section

/-! ## The bit-length size condition `isSizedAt` -/

/-- The bit-length form of the size condition: `0 < n` and `c = (n.toNat.size - 1)/2`, the
algorithm's seed. -/
@[expose] def isSizedAt (n : Int) (c : Nat) :=
  0 < n ∧ c = (n.toNat.size - 1) / 2

/-! ## Initial size condition -/

/-- `n` sits at its own level: `isSizedAt n ((n.toNat.size - 1)/2)`. -/
theorem size_condition_initial {n : Int} (hn : 0 < n) :
    isSizedAt n ((n.toNat.size - 1) / 2) := ⟨hn, rfl⟩

/-! ## Descent of the size condition -/

/-- Descent to any depth `d ≤ c`: right-shifting `isSizedAt n c` by `2(c-d)` gives
`isSizedAt (n >>> 2(c-d)) d`. -/
theorem size_condition_at_depth {n : Int} {c d : Nat} (hd_hi : d ≤ c) (h : isSizedAt n c) :
    isSizedAt (n >>> (2 * (c - d))) d := by
  obtain ⟨hpos, hc⟩ := h
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hpos)
  have hm_pos : 0 < m := by exact_mod_cast hpos
  rw [Int.toNat_natCast] at hc
  have hms : 0 < m.size := Nat.size_pos.mpr hm_pos
  have hk_le : 2 * (c - d) < m.size := by omega
  -- Push the Int shift down to the Nat shift, then read off positivity and the level.
  rw [← Int.natCast_shiftRight]
  refine ⟨?_, ?_⟩
  · exact_mod_cast Nat.shiftRight_pos hk_le
  · rw [Int.toNat_natCast, Nat.size_shiftRight]
    omega

/-- The recursive step `c ↦ ⌊c/2⌋`: right-shifting by `2⌊(c-1)/2⌋+2` lands the level at `c/2` (the
`d = ⌊c/2⌋` case of `size_condition_at_depth`). -/
theorem size_condition_step {n : Int} {c : Nat} (hc : 0 < c) (h : isSizedAt n c) :
    isSizedAt (n >>> (2 * ((c - 1) / 2) + 2)) (c / 2) := by
  rw [show 2 * ((c - 1) / 2) + 2 = 2 * (c - c / 2) from by omega]
  exact size_condition_at_depth (Nat.div_le_self c 2) h

/-! ## Base case -/

/-- Base case: at `c = 0` the size condition forces `n.size ≤ 2`, i.e. `n < 4`, so `1` is a near
square root of `n`. -/
theorem isNearSquareRoot_one_of_isSizedAt {n : Int} (h : isSizedAt n 0) :
    isNearSquareRoot n 1 := by
  obtain ⟨hpos, hc⟩ := h
  have hlt : n.toNat < 4 := by simpa using Nat.size_le.mp (show n.toNat.size ≤ 2 by omega)
  exact ⟨Int.one_pos, by show (1 - 1) * (1 - 1) < n; omega, by show n < (1 + 1) * (1 + 1); omega⟩

end
