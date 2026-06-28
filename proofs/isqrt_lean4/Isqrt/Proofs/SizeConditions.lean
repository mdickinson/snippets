/-
Size-condition lemmas for the isqrt correctness proof.

The "size condition" for `(c, n)` is `4^c ≤ n < 4^(c+1)`. These lemmas
establish:
- the initial size condition holds for `c = (natBitLength n - 1) / 2`,
- the size condition is preserved by the recursive step
  `c ↦ c/2`, `n ↦ n / 2^(2k+2)` where `k = (c-1)/2`,
- `4·M⁴ ≤ n` follows from `4^c ≤ n` for `M = 2^((c-1)/2)`.

The core lemmas are proved at Nat level using the `natBitLength`
infrastructure; the Int-level corollaries at the end, stated in terms of
`hasSizeCondition`, are what the two correctness proofs consume. This file also
owns `isqrt_c_nonneg`, the nonnegativity of the initial recursion depth.
-/

module

public import Isqrt.Definitions.PythonPrimitives
public import Isqrt.Proofs.KeyLemma
import Isqrt.Proofs.PythonPrimitivesLemmas
import Isqrt.Proofs.FDivLemmas

public section

/-! ## Nat-level size conditions -/

/-- Initial size condition: for `0 < n`, the choice
`c = (natBitLength n - 1) / 2` satisfies `4^c ≤ n < 4^(c+1)`. -/
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

/-- Size condition at any depth `d ≤ c`: given `4^c ≤ n < 4^(c+1)`, the
depth-`d` value `n / 4^(c-d)` satisfies `4^d ≤ · < 4^(d+1)`. Proved directly
from the top condition — it cannot be obtained by iterating the single
recursive step `size_condition_step_nat`, whose per-level floor shifts don't
compose to `4^(c-d)` for arbitrary `d`. The step lemma is conversely just the
`d = c/2` corollary of this one. -/
private theorem size_condition_at_depth_nat {c n d : Nat} (hd : d ≤ c)
    (h_lo : 4 ^ c ≤ n) (h_hi : n < 4 ^ (c + 1)) :
    4 ^ d ≤ n / 4 ^ (c - d) ∧ n / 4 ^ (c - d) < 4 ^ (d + 1) := by
  have hpos : 0 < 4 ^ (c - d) := Nat.pow_pos (by decide)
  refine ⟨?_, ?_⟩
  · -- 4^d ≤ n / 4^(c-d)  ⟺  4^d · 4^(c-d) ≤ n
    rw [Nat.le_div_iff_mul_le hpos]
    calc 4 ^ d * 4 ^ (c - d)
        = 4 ^ (d + (c - d)) := by rw [← Nat.pow_add]
      _ = 4 ^ c := by rw [Nat.add_sub_cancel' hd]
      _ ≤ n := h_lo
  · -- n / 4^(c-d) < 4^(d+1)  ⟺  n < 4^(d+1) · 4^(c-d)
    rw [Nat.div_lt_iff_lt_mul hpos]
    calc n
        < 4 ^ (c + 1) := h_hi
      _ = 4 ^ (d + 1 + (c - d)) := by rw [show d + 1 + (c - d) = c + 1 from by omega]
      _ = 4 ^ (d + 1) * 4 ^ (c - d) := by rw [Nat.pow_add]

/-- Size condition preserved by recursive step. Given `4^c ≤ n < 4^(c+1)`
with `0 < c`, the recursive arguments `c' = c/2` and `m = n / 2^(2k+2)`
(where `k = (c-1)/2`) satisfy `4^c' ≤ m < 4^(c'+1)`.

This is `size_condition_at_depth_nat` specialised to depth `d = c/2`: the
step's divisor `2^(2k+2)` equals the depth-`c/2` divisor `4^(c − c/2)`,
since `2k+2 = 2((c-1)/2) + 2 = 2(c − c/2)`, an identity `omega` discharges. -/
private theorem size_condition_step_nat {c n : Nat} (hc : 0 < c)
    (h_lo : 4 ^ c ≤ n) (h_hi : n < 4 ^ (c + 1)) :
    4 ^ (c / 2) ≤ n / 2 ^ (2 * ((c - 1) / 2) + 2) ∧
    n / 2 ^ (2 * ((c - 1) / 2) + 2) < 4 ^ (c / 2 + 1) := by
  -- Bridge the base-2 step divisor to the base-4 depth divisor at `d = c/2`.
  have h_div : 2 ^ (2 * ((c - 1) / 2) + 2) = 4 ^ (c - c / 2) := by
    rw [show (4 : Nat) = 2^2 from rfl, ← Nat.pow_mul]
    -- 2((c-1)/2) + 2 = 2(c − c/2), which omega knows.
    congr 1; omega
  rw [h_div]
  exact size_condition_at_depth_nat (Nat.div_le_self c 2) h_lo h_hi

/-- `4·M⁴ ≤ n` from the size condition's lower bound, where `M = 2^((c-1)/2)`. -/
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

/-! ## Int-level size condition

`hasSizeCondition n c` means `4^c ≤ n < 4^(c+1)`, the invariant maintained
through the `nsqrtRecursive` recursion. The Int-level lemmas are corollaries of
the Nat-level ones, with the bridging done once here. -/

/-- The size condition: `4^c ≤ n < 4^(c+1)`. The level `c` is a `Nat`, so both exponents are
naturals directly and `0 ≤ c` holds by construction; only the value `n` stays an `Int`. -/
@[expose] def hasSizeCondition (n : Int) (c : Nat) : Prop :=
  (4 : Int) ^ c ≤ n ∧ n < (4 : Int) ^ (c + 1)

/-- The size condition forces `0 < n` (since `1 ≤ 4^c ≤ n`). -/
theorem hasSizeCondition.pos {n : Int} {c : Nat} (h : hasSizeCondition n c) : 0 < n := by
  have h0 : (0 : Int) < 4 ^ c := Int.pow_pos (by omega)
  have h1 := h.1
  omega

/-- The size condition forces `0 ≤ n`. -/
private theorem hasSizeCondition.nonneg {n : Int} {c : Nat} (h : hasSizeCondition n c) : 0 ≤ n :=
  Int.le_of_lt h.pos

/-- For a `Nat`-cast value the size condition is exactly its `Nat`-level form. The single
Int↔Nat bridge — now only on the value `n` — the three Int-level corollaries below funnel
through, sparing each its own `exact_mod_cast` unpacking. -/
private theorem hasSizeCondition_natCast_iff {n c : Nat} :
    hasSizeCondition (↑n) c ↔ 4 ^ c ≤ n ∧ n < 4 ^ (c + 1) := by
  unfold hasSizeCondition
  norm_cast

/-- The recursion depth `⌊(n.bit_length() - 1) / 2⌋` is nonneg for nonzero `n` — the
seed `c` both isqrt formulations hand to the recursion, paired at the same `c` with
`size_condition_initial` just below. Stated in pure `Int.fdiv` form (the `Except` `//`,
`pyFloordiv`, reduces to it on its `.ok` branch), so both formulations share it. -/
theorem isqrt_c_nonneg {n : Int} (hn : n ≠ 0) :
    0 ≤ Int.fdiv (n.bitLength - 1) 2 :=
  Int.fdiv_nonneg (by have := Int.bitLength_pos hn; omega) (by omega)

/-- Initial size condition holds for the Nat seed `c = ⌊(n.bitLength - 1) / 2⌋.toNat`. The lone
`.toNat` is the boundary between the algorithm's `Int` seed and the proof's `Nat` level; the
consumers reconcile their `Int` seed with `↑c` via `isqrt_c_nonneg`. -/
theorem size_condition_initial {n : Int} (hn : 0 < n) :
    hasSizeCondition n (Int.fdiv (n.bitLength - 1) 2).toNat := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hn)
  have hm_pos : 0 < m := by exact_mod_cast hn
  have h_bl_pos : 1 ≤ natBitLength m := natBitLength_pos_iff.mpr hm_pos
  -- Convert recursion-depth expression to Nat.
  have h_toNat : (Int.fdiv ((↑m : Int).bitLength - 1) 2).toNat
                  = (natBitLength m - 1) / 2 := by
    rw [Int.bitLength_natCast,
        show ((natBitLength m : Nat) : Int) - 1 = ((natBitLength m - 1 : Nat) : Int) from by
          omega,
        show ((2 : Int)) = ((2 : Nat) : Int) from rfl,
        Int.toNat_fdiv_of_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)]
    rfl
  rw [h_toNat, hasSizeCondition_natCast_iff]
  exact size_condition_initial_nat hm_pos

/-- Size condition preserved by the recursive step: `c ↦ ⌊c/2⌋`, `n ↦ ⌊n / 4M²⌋` where the
step's scaler is `M = 2^⌊(c-1)/2⌋`. The `4M²` denominator is the Python shift `2^(2⌊(c-1)/2⌋+2)`
the recursion divides by, written in the form `key_isqrt_lemma` consumes. -/
theorem size_condition_step {n M : Int} {c : Nat} (hM : M = 2 ^ ((c - 1) / 2))
    (hc : 0 < c) (h : hasSizeCondition n c) :
    hasSizeCondition (Int.fdiv n (4 * M ^ 2)) (c / 2) := by
  -- Read the `4M²` denominator as the Python shift `2^(2k+2)`, then descend in shift form.
  rw [hM, four_mul_two_pow_sq ((c - 1) / 2)]
  obtain ⟨nn, rfl⟩ := Int.eq_ofNat_of_zero_le h.nonneg
  obtain ⟨h_lo_nat, h_hi_nat⟩ := hasSizeCondition_natCast_iff.mp h
  -- The shifted value equals the Int-cast of the Nat-level shifted value.
  have h_shift : Int.fdiv (↑nn : Int) (2 ^ (2 * ((c - 1) / 2) + 2))
      = ((nn / 2 ^ (2 * ((c - 1) / 2) + 2) : Nat) : Int) := by
    rw [show ((2 : Int) ^ (2 * ((c - 1) / 2) + 2))
          = ((2 ^ (2 * ((c - 1) / 2) + 2) : Nat) : Int) by push_cast; rfl,
        Int.fdiv_natCast_natCast]
  rw [h_shift, hasSizeCondition_natCast_iff]
  exact size_condition_step_nat hc h_lo_nat h_hi_nat

/-- `4 * M^4 ≤ n` from the size condition, where `M = 2^⌊(c-1)/2⌋`. -/
theorem M_bound_from_size {n : Int} {c : Nat} (hc : 0 < c) (h : hasSizeCondition n c) :
    4 * ((2 : Int) ^ ((c - 1) / 2)) ^ 4 ≤ n := by
  obtain ⟨nn, rfl⟩ := Int.eq_ofNat_of_zero_le h.nonneg
  obtain ⟨h_lo_nat, _⟩ := hasSizeCondition_natCast_iff.mp h
  exact_mod_cast M_bound_from_size_nat hc h_lo_nat

/-- A suitable scaler from the size condition: for `0 < c` with `4^c ≤ n < 4^(c+1)`, the step's
scaler `M = 2^⌊(c-1)/2⌋` is suitable for `n` — positivity is immediate, and the `4M⁴ ≤ n` bound
is `M_bound_from_size`. This is the form the key lemma consumes. -/
theorem isSuitableScaler_of_hasSizeCondition {n M : Int} {c : Nat}
    (hM : M = 2 ^ ((c - 1) / 2)) (hc : 0 < c) (h : hasSizeCondition n c) :
    isSuitableScaler n M := by
  subst hM
  exact ⟨Int.pow_pos (by omega), M_bound_from_size hc h⟩

/-- Base case of the recursion: at `c = 0` the size condition `1 ≤ n < 4` makes `1` a near
square root of `n`. The counterpart to the step-case bridge
`isSuitableScaler_of_hasSizeCondition`. -/
theorem isNearSquareRoot_one_of_hasSizeCondition {n : Int} (h : hasSizeCondition n 0) :
    isNearSquareRoot n 1 := by
  obtain ⟨h_lo, h_hi⟩ := h
  simp only [Nat.zero_add, Int.pow_zero, Int.pow_one] at h_lo h_hi
  exact ⟨by show (1 - 1) * (1 - 1) < n; omega, by show n < (1 + 1) * (1 + 1); omega⟩

/-! ## Size condition at depth -/

/-- The value `⌊n / 4^(c-d)⌋` at depth `d` (`0 ≤ d ≤ c`) inherits the size condition from
`hasSizeCondition n c`, now at level `d`. The construction proof behind `SizedProblem.subAt`, and
the `(n,c)`-only fact the seed and step of both loop invariants lean on. -/
theorem size_condition_at_depth {n : Int} {c d : Nat} (hd_hi : d ≤ c)
    (h : hasSizeCondition n c) :
    hasSizeCondition (n.fdiv (4 ^ (c - d))) d := by
  obtain ⟨nn, rfl⟩ := Int.eq_ofNat_of_zero_le h.nonneg
  -- The fdiv of nonneg-nat casts is the natCast of the Nat division.
  have h_bridge : Int.fdiv (↑nn : Int) ((4 : Int) ^ (c - d))
      = ((nn / 4 ^ (c - d) : Nat) : Int) := by
    rw [show ((4 : Int) ^ (c - d)) = ((4 ^ (c - d) : Nat) : Int) from by push_cast; rfl,
        Int.fdiv_natCast_natCast]
  obtain ⟨h_lo_nat, h_hi_nat⟩ := hasSizeCondition_natCast_iff.mp h
  rw [h_bridge, hasSizeCondition_natCast_iff]
  exact size_condition_at_depth_nat hd_hi h_lo_nat h_hi_nat

end
