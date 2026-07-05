/-
The bit-length invariant `isSizedAt n c` (`0 < n ∧ c = (n.toNat.size - 1)/2`) and its descent, and
the `SizedProblem` structure carrying it, with the shift-form operations `descend` / `newtonLift`
both correctness proofs build on.
-/

module

public import Isqrt.Proofs.NatSize
public import Isqrt.Proofs.SupportLemmas
import Isqrt.Proofs.PythonTranslation

public section

/-! ## The bit-length size condition `isSizedAt` -/

/-- The bit-length form of the size condition: `0 < n` and `c = (n.toNat.size - 1)/2`, the
algorithm's seed. -/
@[expose] def isSizedAt (n : Int) (c : Nat) :=
  0 < n ∧ c = (n.toNat.size - 1) / 2

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
private theorem size_condition_step {n : Int} {c : Nat} (hc : 0 < c) (h : isSizedAt n c) :
    isSizedAt (n >>> (2 * ((c - 1) / 2) + 2)) (c / 2) := by
  rw [show 2 * ((c - 1) / 2) + 2 = 2 * (c - c / 2) from by omega]
  exact size_condition_at_depth (Nat.div_le_self c 2) h

/-! ## The sized problem -/

/-- A *sized problem*: a value `n`, a recursion level `c`, and the size invariant `isSizedAt n c`
relating them. -/
@[ext] structure SizedProblem where
  /-- The value whose near square root is sought (at this recursion level). -/
  n : Int
  /-- The recursion level. -/
  c : Nat
  /-- The size invariant `isSizedAt n c` in bit-length form. -/
  hsize : isSizedAt n c

namespace SizedProblem

-- The operations below are intentionally unexposed, so clients go through the equation lemmas
-- rather than unfolding shift arithmetic. Those lemmas are proved with `(rfl)`, not `rfl`, to stay
-- propositional — bare `rfl` would force the operations to be exposed. See
-- https://github.com/leanprover/lean4/issues/12803.

/-- The seed problem for a positive `n`: the value `n` at its own level `(n.toNat.size - 1)/2`. -/
def ofPos {n : Int} (hn : 0 < n) : SizedProblem :=
  ⟨n, (n.toNat.size - 1) / 2, hn, rfl⟩

/-- The seed problem's value is `n`. -/
theorem ofPos_n {n : Int} (hn : 0 < n) : (ofPos hn).n = n := (rfl)

/-- The seed problem's level is `(n.toNat.size - 1)/2`. -/
theorem ofPos_c {n : Int} (hn : 0 < n) : (ofPos hn).c = (n.toNat.size - 1) / 2 := (rfl)

/-- The step shift amount `⌊(c-1)/2⌋`. -/
def shifter (p : SizedProblem) : Nat := (p.c - 1) / 2

/-- The step shift amount in closed form. -/
theorem shifter_eq (p : SizedProblem) : p.shifter = (p.c - 1) / 2 := (rfl)

/-- One reduction step: `(n, c) ↦ (n >>> (2·shifter+2), ⌊c/2⌋)`, carrying the invariant to the
child. -/
def descend (p : SizedProblem) (hc : 0 < p.c) : SizedProblem :=
  ⟨p.n >>> (2 * p.shifter + 2), p.c / 2, size_condition_step hc p.hsize⟩

/-- The descended value in shift form. -/
theorem descend_n (p : SizedProblem) (hc : 0 < p.c) :
    (p.descend hc).n = p.n >>> (2 * p.shifter + 2) := (rfl)

/-- The descended level is `⌊c/2⌋`. -/
theorem descend_c (p : SizedProblem) (hc : 0 < p.c) : (p.descend hc).c = p.c / 2 := (rfl)

/-- Descending strictly lowers the level, so the recursion terminates. -/
theorem descend_lt (p : SizedProblem) (hc : 0 < p.c) : (p.descend hc).c < p.c := by
  rw [descend_c]; exact Nat.div_lt_self hc (by decide)

/-- The Newton combine lifting a value `a` for the descended problem back to `p`:
`(a <<< shifter) + ⌊(n >>> shifter+2) / a⌋`. -/
def newtonLift (p : SizedProblem) (a : Int) : Int :=
  (a <<< p.shifter) + (p.n >>> (p.shifter + 2)) / a

/-- The Newton lift in shift form. -/
theorem newtonLift_eq (p : SizedProblem) (a : Int) :
    p.newtonLift a = a <<< p.shifter + (p.n >>> (p.shifter + 2)) / a := (rfl)

end SizedProblem

end
