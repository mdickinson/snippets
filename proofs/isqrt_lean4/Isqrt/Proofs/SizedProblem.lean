/-
The bit-length invariant `isSizedAt n c` (`0 < n ∧ c = (n.toNat.size - 1)/2`) and its descent, and
the `SizedProblem` structure carrying it, with the shift-form operations `descend` / `newtonLift` /
`subAt` both correctness proofs run.
-/

module

public import Isqrt.Definitions.Specification
public import Isqrt.Proofs.SupportLemmas
import Isqrt.Proofs.PythonTranslation

public section

/-! ## The bit-length size condition `isSizedAt` -/

/-- The bit-length form of the size condition: `0 < n` and `c = (n.toNat.size - 1)/2`, the
algorithm's seed. -/
@[expose] def isSizedAt (n : Int) (c : Nat) :=
  0 < n ∧ c = (n.toNat.size - 1) / 2

/-- `n` sits at its own level: `isSizedAt n ((n.toNat.size - 1)/2)`. -/
theorem size_condition_initial {n : Int} (hn : 0 < n) :
    isSizedAt n ((n.toNat.size - 1) / 2) := ⟨hn, rfl⟩

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

/-- Base case: at `c = 0` the size condition forces `n.size ≤ 2`, i.e. `n < 4`, so `1` is a near
square root of `n`. -/
theorem isNearSquareRoot_one_of_isSizedAt {n : Int} (h : isSizedAt n 0) :
    isNearSquareRoot n 1 := by
  obtain ⟨hpos, hc⟩ := h
  have hlt : n.toNat < 4 := by simpa using Nat.size_le.mp (show n.toNat.size ≤ 2 by omega)
  exact ⟨Int.one_pos, by show (1 - 1) * (1 - 1) < n; omega, by show n < (1 + 1) * (1 + 1); omega⟩

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

/-- The step shift amount `⌊(c-1)/2⌋`. -/
@[expose] def shifter (p : SizedProblem) : Nat := (p.c - 1) / 2

/-- One reduction step: `(n, c) ↦ (n >>> (2·shifter+2), ⌊c/2⌋)`, carrying the invariant to the
child. -/
@[expose] def descend (p : SizedProblem) (hc : 0 < p.c) : SizedProblem :=
  ⟨p.n >>> (2 * p.shifter + 2), p.c >>> 1, size_condition_step hc p.hsize⟩

/-- The Newton combine lifting a value `a` for the descended problem back to `p`:
`(a <<< shifter) + ⌊(n >>> shifter+2) / a⌋`. -/
@[expose] def newtonLift (p : SizedProblem) (a : Int) : Int :=
  (a <<< p.shifter) + (p.n >>> (p.shifter + 2)) / a

/-- The depth-`d` subproblem (`d ≤ p.c`): value `p.n >>> 2(c-d)` at level `d`, with the inherited
invariant. -/
@[expose] def subAt (p : SizedProblem) (d : Nat) (hhi : d ≤ p.c) : SizedProblem :=
  ⟨p.n >>> (2 * (p.c - d)), d, size_condition_at_depth hhi p.hsize⟩

/-- Descending the depth-`d` subproblem gives the depth-`⌊d/2⌋` one:
`descend (p.subAt d) = p.subAt ⌊d/2⌋`. -/
theorem descend_subAt {p : SizedProblem} {d : Nat} (hhi : d ≤ p.c) (hd_pos : 0 < d) :
    (p.subAt d hhi).descend hd_pos
      = p.subAt (d >>> 1) (Nat.le_trans (Nat.shiftRight_le d 1) hhi) := by
  apply SizedProblem.ext
  · show (p.n >>> (2 * (p.c - d))) >>> (2 * ((d - 1) / 2) + 2) = p.n >>> (2 * (p.c - d / 2))
    rw [← Int.shiftRight_add,
        show 2 * (p.c - d) + (2 * ((d - 1) / 2) + 2) = 2 * (p.c - d / 2) from by omega]
  · rfl

/-- The decoded loop body is the Newton lift of the depth-`d` subproblem: with child shift
`e = ⌊d/2⌋`, `(a <<< d-e-1) + ⌊(p.n >>> 2c-e-d+1) / a⌋ = (p.subAt d).newtonLift a`. -/
theorem subAt_body_eq {p : SizedProblem} {d e : Nat} {a : Int} (hhi : d ≤ p.c)
    (he : e = d >>> 1) (hd_pos : 0 < d) :
    a <<< (d - e - 1) + (p.n >>> (2 * p.c - e - d + 1)) / a
      = (p.subAt d hhi).newtonLift a := by
  -- `d >>> 1` is `d / 2`; restate the child shift so the arithmetic below reads the division.
  have he : e = d / 2 := he
  show a <<< (d - e - 1) + (p.n >>> (2 * p.c - e - d + 1)) / a
      = a <<< ((d - 1) / 2) + ((p.n >>> (2 * (p.c - d))) >>> ((d - 1) / 2 + 2)) / a
  rw [← Int.shiftRight_add,
      show d - e - 1 = (d - 1) / 2 from by omega,
      show 2 * p.c - e - d + 1 = 2 * (p.c - d) + ((d - 1) / 2 + 2) from by omega]

end SizedProblem

end
