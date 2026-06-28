/-
Size-condition lemmas for the isqrt correctness proof.

`SizedProblem` carries `isSizedAt n c` — `0 < n ∧ c = ⌊log₂ n / 2⌋`, the bit-length form of
"`n` sits at level `c`", matching the algorithm's seed `c = (n.bit_length() - 1) // 2`. The key
lemma instead wants the power bound `hasSizeCondition n c` (`4^c ≤ n < 4^(c+1)`);
`hasSizeCondition_of_isSizedAt` bridges the two once, so `SizedProblem` builds its instances in
the shift/bit-length language its operations speak while the key-lemma side reads the power bound.

These lemmas establish:
- the seed `c = ⌊(n.bitLength - 1)/2⌋` satisfies `isSizedAt n c` (`size_condition_initial`),
- `isSizedAt` descends: dividing by the depth-`d` shift `2^(2(c-d))` lowers the level to `d`
  (`size_condition_at_depth`), of which the recursive step `c ↦ c/2` is the `d = c/2` case
  (`size_condition_step`),
- `isSizedAt n c → hasSizeCondition n c` (`hasSizeCondition_of_isSizedAt`), and from the power
  bound `4·M⁴ ≤ n` for `M = 2^((c-1)/2)` (`M_bound_from_size` → `isSuitableScaler_of_hasSizeCondition`).

The bit-length core (`log2_div_two_pow`, `natBitLength`) lives in `PythonPrimitivesLemmas`; this
file adds the Int-level `isSizedAt` theory and the bridge to the power bound.
-/

module

public import Isqrt.Definitions.PythonPrimitives
public import Isqrt.Proofs.KeyLemma
import Isqrt.Proofs.PythonPrimitivesLemmas
import Isqrt.Proofs.FDivLemmas

public section

/-! ## Nat-level power bounds -/

/-- Initial power bound: for `0 < n`, the choice `c = (natBitLength n - 1) / 2` satisfies
`4^c ≤ n < 4^(c+1)`. The engine behind `hasSizeCondition_of_isSizedAt`. -/
private theorem size_condition_initial_nat {n : Nat} (hn : 0 < n) :
    4 ^ ((natBitLength n - 1) / 2) ≤ n ∧
    n < 4 ^ ((natBitLength n - 1) / 2 + 1) := by
  -- Below, b = natBitLength n and c = ⌊(b-1)/2⌋ (spelled out in full).
  have hb_pos : 0 < natBitLength n := natBitLength_pos_iff.mpr hn
  refine ⟨?_, ?_⟩
  · -- 4^c = 2^(2c) ≤ 2^(b-1) ≤ n
    calc 4 ^ ((natBitLength n - 1) / 2)
        = 2 ^ (2 * ((natBitLength n - 1) / 2)) := by
          rw [show (4 : Nat) = 2^2 from rfl, ← Nat.pow_mul]
      _ ≤ 2 ^ (natBitLength n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ n := two_pow_pred_natBitLength_le hn
  · -- n < 2^b ≤ 2^(2(c+1)) = 4^(c+1)
    calc n
        < 2 ^ natBitLength n := lt_two_pow_natBitLength n
      _ ≤ 2 ^ (2 * ((natBitLength n - 1) / 2 + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 4 ^ ((natBitLength n - 1) / 2 + 1) := by
          rw [show (4 : Nat) = 2^2 from rfl, ← Nat.pow_mul]

/-- `4·M⁴ ≤ n` from the power bound's lower bound, where `M = 2^((c-1)/2)`. -/
private theorem M_bound_from_size_nat {c n : Nat} (hc : 0 < c) (h_lo : 4 ^ c ≤ n) :
    4 * (2 ^ ((c - 1) / 2)) ^ 4 ≤ n := by
  -- Below, k = ⌊(c-1)/2⌋ (spelled out in full).
  calc 4 * (2 ^ ((c - 1) / 2)) ^ 4
      = 2 ^ (4 * ((c - 1) / 2) + 2) := by
        rw [show (4 : Nat) = 2^2 from rfl, ← Nat.pow_mul, ← Nat.pow_add]
        congr 1; omega
    _ ≤ 2 ^ (2 * c) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 4 ^ c := by rw [show (4 : Nat) = 2^2 from rfl, ← Nat.pow_mul]
    _ ≤ n := h_lo

/-! ## The power bound `hasSizeCondition`

`hasSizeCondition n c` means `4^c ≤ n < 4^(c+1)`, the form `key_isqrt_lemma` consumes.
`SizedProblem` carries the bit-length `isSizedAt` (below) and exposes this as the derived `.hsc`. -/

/-- The power bound: `4^c ≤ n < 4^(c+1)`. The level `c` is a `Nat`, so both exponents are naturals
directly and `0 ≤ c` holds by construction; only the value `n` stays an `Int`. -/
@[expose] def hasSizeCondition (n : Int) (c : Nat) : Prop :=
  (4 : Int) ^ c ≤ n ∧ n < (4 : Int) ^ (c + 1)

/-- The power bound forces `0 < n` (since `1 ≤ 4^c ≤ n`). -/
theorem hasSizeCondition.pos {n : Int} {c : Nat} (h : hasSizeCondition n c) : 0 < n := by
  have h0 : (0 : Int) < 4 ^ c := Int.pow_pos (by omega)
  have h1 := h.1
  omega

/-- The power bound forces `0 ≤ n`. -/
private theorem hasSizeCondition.nonneg {n : Int} {c : Nat} (h : hasSizeCondition n c) : 0 ≤ n :=
  Int.le_of_lt h.pos

/-- For a `Nat`-cast value the power bound is exactly its `Nat`-level form. The single Int↔Nat
bridge — now only on the value `n` — the Int-level corollaries below funnel through, sparing each
its own `exact_mod_cast` unpacking. -/
private theorem hasSizeCondition_natCast_iff {n c : Nat} :
    hasSizeCondition (↑n) c ↔ 4 ^ c ≤ n ∧ n < 4 ^ (c + 1) := by
  unfold hasSizeCondition
  norm_cast

/-! ## The bit-length size condition `isSizedAt` -/

/-- The size condition in bit-length form: `n` is positive and `c` is its level `⌊log₂ n / 2⌋`
(equivalently `⌊(n.bit_length() - 1) / 2⌋`, the algorithm's seed). This is what `SizedProblem`
carries, so its instances are built in the shift/bit-length language the operations speak rather
than in the power bound `hasSizeCondition`. The two are equivalent (`hasSizeCondition_of_isSizedAt`). -/
@[expose] def isSizedAt (n : Int) (c : Nat) : Prop :=
  0 < n ∧ c = n.toNat.log2 / 2

/-- `isSizedAt` forces `0 < n` (by definition). -/
theorem isSizedAt.pos {n : Int} {c : Nat} (h : isSizedAt n c) : 0 < n := h.1

/-- The bridge from the bit-length size condition to the power bound: `isSizedAt n c` gives
`4^c ≤ n < 4^(c+1)`. The single place the two forms cross — `SizedProblem.hsc` is this applied to
the structure's `hsize` field. Reduces to `size_condition_initial_nat` after rewriting `c` back to
`(natBitLength n.toNat - 1)/2` via the `bitLength = log2 + 1` off-by-one (`natBitLength_sub_one`). -/
theorem hasSizeCondition_of_isSizedAt {n : Int} {c : Nat} (h : isSizedAt n c) :
    hasSizeCondition n c := by
  obtain ⟨hpos, hc⟩ := h
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hpos)
  have hm_pos : 0 < m := by exact_mod_cast hpos
  rw [Int.toNat_natCast] at hc
  rw [hasSizeCondition_natCast_iff, hc, ← natBitLength_sub_one hm_pos]
  exact size_condition_initial_nat hm_pos

/-! ## Initial size condition and recursion depth -/

/-- The recursion depth `⌊(n.bit_length() - 1) / 2⌋` is nonneg for nonzero `n` — the
seed `c` both isqrt formulations hand to the recursion, paired at the same `c` with
`size_condition_initial` just below. Stated in pure `Int.fdiv` form (the `Except` `//`,
`pyFloordiv`, reduces to it on its `.ok` branch), so both formulations share it. -/
theorem isqrt_c_nonneg {n : Int} (hn : n ≠ 0) :
    0 ≤ Int.fdiv (n.bitLength - 1) 2 :=
  Int.fdiv_nonneg (by have := Int.bitLength_pos hn; omega) (by omega)

/-- Initial size condition for the Nat seed `c = ⌊(n.bitLength - 1)/2⌋.toNat`: this `c` is exactly
`n`'s level `⌊log₂ n / 2⌋`, so `isSizedAt` holds almost by definition — the lone step is the
`bitLength = log2 + 1` off-by-one (`natBitLength_sub_one`). The consumers reconcile their `Int` seed
with `↑c` via `isqrt_c_nonneg`. -/
theorem size_condition_initial {n : Int} (hn : 0 < n) :
    isSizedAt n (Int.fdiv (n.bitLength - 1) 2).toNat := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hn)
  have hm_pos : 0 < m := by exact_mod_cast hn
  have hbl : 1 ≤ natBitLength m := natBitLength_pos_iff.mpr hm_pos
  refine ⟨hn, ?_⟩
  rw [Int.toNat_natCast, ← natBitLength_sub_one hm_pos, Int.bitLength_natCast,
      show ((natBitLength m : Nat) : Int) - 1 = ((natBitLength m - 1 : Nat) : Int) from by omega,
      show ((2 : Int)) = ((2 : Nat) : Int) from rfl,
      Int.toNat_fdiv_of_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)]
  simp only [Int.toNat_natCast]

/-! ## Descent of the size condition -/

/-- Size condition at any depth `d ≤ c`: given `isSizedAt n c`, dividing by the depth-`d` shift
`2^(2(c-d))` lowers the level to `d`. The bit-length core: dividing by `2^(2(c-d))` drops
`2(c-d)` bits, so `log₂` falls by `2(c-d)` and the level `⌊log₂/2⌋` falls by `c-d` to `d`
(`log2_div_two_pow`). The construction proof behind `SizedProblem.subAt`. -/
theorem size_condition_at_depth {n : Int} {c d : Nat} (hd_hi : d ≤ c) (h : isSizedAt n c) :
    isSizedAt (n.fdiv (2 ^ (2 * (c - d)))) d := by
  obtain ⟨hpos, hc⟩ := h
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hpos)
  have hm_pos : 0 < m := by exact_mod_cast hpos
  rw [Int.toNat_natCast] at hc
  have hk_le : 2 * (c - d) ≤ m.log2 := by omega
  -- The fdiv of nonneg-nat casts is the natCast of the Nat division.
  have hval : (↑m : Int).fdiv (2 ^ (2 * (c - d))) = ↑(m / 2 ^ (2 * (c - d))) := by
    rw [show ((2 : Int) ^ (2 * (c - d))) = ((2 ^ (2 * (c - d)) : Nat) : Int) from by push_cast; rfl,
        Int.fdiv_natCast_natCast]
  have h2k_le : 2 ^ (2 * (c - d)) ≤ m :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) hk_le) (Nat.log2_self_le (Nat.ne_of_gt hm_pos))
  refine ⟨?_, ?_⟩
  · rw [hval]; exact_mod_cast Nat.div_pos h2k_le (Nat.pow_pos (by decide))
  · rw [hval, Int.toNat_natCast, log2_div_two_pow hm_pos hk_le]; omega

/-- Size condition preserved by the recursive step `c ↦ ⌊c/2⌋`: dividing by the step's shift
`2^(2⌊(c-1)/2⌋+2)` (the `4M²` denominator for `M = 2^⌊(c-1)/2⌋`) lands the level at `c/2`. The
`d = c/2` case of `size_condition_at_depth`, since the step shift equals the depth-`c/2` shift
`2^(2(c - c/2))` — an identity `omega` discharges. -/
theorem size_condition_step {n : Int} {c : Nat} (hc : 0 < c) (h : isSizedAt n c) :
    isSizedAt (n.fdiv (2 ^ (2 * ((c - 1) / 2) + 2))) (c / 2) := by
  rw [show 2 * ((c - 1) / 2) + 2 = 2 * (c - c / 2) from by omega]
  exact size_condition_at_depth (Nat.div_le_self c 2) h

/-! ## Consequences of the power bound -/

/-- `4 * M^4 ≤ n` from the power bound, where `M = 2^⌊(c-1)/2⌋`. -/
theorem M_bound_from_size {n : Int} {c : Nat} (hc : 0 < c) (h : hasSizeCondition n c) :
    4 * ((2 : Int) ^ ((c - 1) / 2)) ^ 4 ≤ n := by
  obtain ⟨nn, rfl⟩ := Int.eq_ofNat_of_zero_le h.nonneg
  obtain ⟨h_lo_nat, _⟩ := hasSizeCondition_natCast_iff.mp h
  exact_mod_cast M_bound_from_size_nat hc h_lo_nat

/-- A suitable scaler from the power bound: for `0 < c` with `4^c ≤ n < 4^(c+1)`, the step's
scaler `M = 2^⌊(c-1)/2⌋` is suitable for `n` — positivity is immediate, and the `4M⁴ ≤ n` bound
is `M_bound_from_size`. This is the form the key lemma consumes. -/
theorem isSuitableScaler_of_hasSizeCondition {n M : Int} {c : Nat}
    (hM : M = 2 ^ ((c - 1) / 2)) (hc : 0 < c) (h : hasSizeCondition n c) :
    isSuitableScaler n M := by
  subst hM
  exact ⟨Int.pow_pos (by omega), M_bound_from_size hc h⟩

/-- Base case of the recursion: at `c = 0` the power bound `1 ≤ n < 4` makes `1` a near
square root of `n`. The counterpart to the step-case bridge
`isSuitableScaler_of_hasSizeCondition`. -/
theorem isNearSquareRoot_one_of_hasSizeCondition {n : Int} (h : hasSizeCondition n 0) :
    isNearSquareRoot n 1 := by
  obtain ⟨h_lo, h_hi⟩ := h
  simp only [Nat.zero_add, Int.pow_zero, Int.pow_one] at h_lo h_hi
  exact ⟨by show (1 - 1) * (1 - 1) < n; omega, by show n < (1 + 1) * (1 + 1); omega⟩

end
