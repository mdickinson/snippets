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

meta import Mathlib.Tactic.Ring
meta import Mathlib.Tactic.Positivity
meta import Mathlib.Tactic.Linarith
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
  set b := natBitLength n with hb_def
  set c := (b - 1) / 2 with hc_def
  have hb_pos : 0 < b := natBitLength_pos_iff.mpr hn
  refine ⟨?_, ?_⟩
  · -- 4^c ≤ n: 4^c = 2^(2c) ≤ 2^(b-1) ≤ n
    calc 4 ^ c
        = 2 ^ (2 * c) := by rw [show (4 : Nat) = 2^2 from rfl, ← pow_mul]
      _ ≤ 2 ^ (b - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ n := two_pow_pred_natBitLength_le hn
  · -- n < 4^(c+1): n < 2^b ≤ 2^(2*(c+1)) = 4^(c+1)
    calc n
        < 2 ^ b := lt_two_pow_natBitLength n
      _ ≤ 2 ^ (2 * (c + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 4 ^ (c + 1) := by rw [show (4 : Nat) = 2^2 from rfl, ← pow_mul]

/-- Size condition at any depth `d ≤ c`: given `4^c ≤ n < 4^(c+1)`, the
depth-`d` value `n / 4^(c-d)` satisfies `4^d ≤ · < 4^(d+1)`. Proved directly
from the top condition — it cannot be obtained by iterating the single
recursive step `size_condition_step_nat`, whose per-level floor shifts don't
compose to `4^(c-d)` for arbitrary `d`. The step lemma is conversely just the
`d = c/2` corollary of this one. -/
private theorem size_condition_at_depth_nat {c n d : Nat} (hd : d ≤ c)
    (h_lo : 4 ^ c ≤ n) (h_hi : n < 4 ^ (c + 1)) :
    4 ^ d ≤ n / 4 ^ (c - d) ∧ n / 4 ^ (c - d) < 4 ^ (d + 1) := by
  have hpos : 0 < 4 ^ (c - d) := by positivity
  refine ⟨?_, ?_⟩
  · -- 4^d ≤ n / 4^(c-d)  ⟺  4^d · 4^(c-d) ≤ n
    rw [Nat.le_div_iff_mul_le hpos]
    calc 4 ^ d * 4 ^ (c - d)
        = 4 ^ (d + (c - d)) := by rw [← pow_add]
      _ = 4 ^ c := by rw [Nat.add_sub_cancel' hd]
      _ ≤ n := h_lo
  · -- n / 4^(c-d) < 4^(d+1)  ⟺  n < 4^(d+1) · 4^(c-d)
    rw [Nat.div_lt_iff_lt_mul hpos]
    calc n
        < 4 ^ (c + 1) := h_hi
      _ = 4 ^ (d + 1 + (c - d)) := by rw [show d + 1 + (c - d) = c + 1 from by omega]
      _ = 4 ^ (d + 1) * 4 ^ (c - d) := by rw [pow_add]

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
    rw [show (4 : Nat) = 2^2 from rfl, ← pow_mul]
    -- 2((c-1)/2) + 2 = 2(c − c/2), which omega knows.
    congr 1; omega
  rw [h_div]
  exact size_condition_at_depth_nat (Nat.div_le_self c 2) h_lo h_hi

/-- `4·M⁴ ≤ n` from the size condition's lower bound, where `M = 2^((c-1)/2)`. -/
private theorem M_bound_from_size_nat {c n : Nat} (hc : 0 < c) (h_lo : 4 ^ c ≤ n) :
    4 * (2 ^ ((c - 1) / 2)) ^ 4 ≤ n := by
  set k := (c - 1) / 2 with hk_def
  calc 4 * (2 ^ k) ^ 4
      = 2 ^ (4 * k + 2) := by
        rw [show (4 : Nat) = 2^2 from rfl, ← pow_mul, ← pow_add]
        congr 1; ring
    _ ≤ 2 ^ (2 * c) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 4 ^ c := by rw [show (4 : Nat) = 2^2 from rfl, ← pow_mul]
    _ ≤ n := h_lo

/-! ## Int-level size condition

`hasSizeCondition n c` means `4^c ≤ n < 4^(c+1)`, the invariant maintained
through the `nsqrtRecursive` recursion. The Int-level lemmas are corollaries of
the Nat-level ones, with the bridging done once here. -/

/-- The size condition: `4^c ≤ n < 4^(c+1)` (using `toNat` so the exponents are naturals).
The upper bound is written `4^(c+1).toNat`, not `4^(c.toNat + 1)`, so that `0 ≤ c` is a
*consequence* (`hasSizeCondition.c_nonneg`): for `c < 0` both exponents collapse to `0` and
the bounds `1 ≤ n < 1` are unsatisfiable. For `0 ≤ c` the two forms agree. -/
@[expose] def hasSizeCondition (n c : Int) : Prop :=
  (4 : Int) ^ c.toNat ≤ n ∧ n < (4 : Int) ^ (c + 1).toNat

/-- The size condition forces `0 < n` (since `1 ≤ 4^c.toNat ≤ n`). -/
theorem hasSizeCondition.pos {n c : Int} (h : hasSizeCondition n c) : 0 < n := by
  have : (0 : Int) < 4 ^ c.toNat := by positivity
  linarith [h.1]

/-- The size condition forces `0 ≤ n`. -/
private theorem hasSizeCondition.nonneg {n c : Int} (h : hasSizeCondition n c) : 0 ≤ n :=
  h.pos.le

/-- The size condition forces `0 ≤ c`: the bounds give `4^c.toNat < 4^(c+1).toNat`, but for
`c < 0` both exponents are `0`, leaving `4^0 < 4^0`. -/
theorem hasSizeCondition.c_nonneg {n c : Int} (h : hasSizeCondition n c) : 0 ≤ c := by
  obtain ⟨h_lo, h_hi⟩ := h
  have hlt : (4 : Int) ^ c.toNat < (4 : Int) ^ (c + 1).toNat := lt_of_le_of_lt h_lo h_hi
  by_contra hc
  have e1 : c.toNat = 0 := by omega
  have e2 : (c + 1).toNat = 0 := by omega
  rw [e1, e2] at hlt
  exact absurd hlt (lt_irrefl _)

/-- Construct a size condition from the `c.toNat + 1` form of the upper bound, given `0 ≤ c`
(for which `4^(c+1).toNat = 4^(c.toNat + 1)`). Lets the construction sites below work in the
simpler `c.toNat` form. -/
private theorem hasSizeCondition_of_toNat {n c : Int} (hc : 0 ≤ c)
    (h_lo : (4 : Int) ^ c.toNat ≤ n) (h_hi : n < (4 : Int) ^ (c.toNat + 1)) :
    hasSizeCondition n c :=
  ⟨h_lo, by rwa [show (c + 1).toNat = c.toNat + 1 from by omega]⟩

/-- For `Nat`-cast arguments the size condition is exactly its `Nat`-level form. The single
Int↔Nat bridge the three Int-level corollaries below funnel through, sparing each its own
`Int.eq_ofNat_of_zero_le` / `exact_mod_cast` unpacking. -/
private theorem hasSizeCondition_natCast_iff {n c : Nat} :
    hasSizeCondition (↑n) (↑c) ↔ 4 ^ c ≤ n ∧ n < 4 ^ (c + 1) := by
  unfold hasSizeCondition
  rw [Int.toNat_natCast,
      show ((c : Int) + 1) = ((c + 1 : Nat) : Int) by push_cast; ring, Int.toNat_natCast]
  norm_cast

/-- The recursion depth `⌊(n.bit_length() - 1) / 2⌋` is nonneg for nonzero `n` — the
seed `c` both isqrt formulations hand to the recursion, paired at the same `c` with
`size_condition_initial` just below. Stated in pure `Int.fdiv` form (the `Except` `//`,
`pyFloordiv`, reduces to it on its `.ok` branch), so both formulations share it. -/
theorem isqrt_c_nonneg {n : Int} (hn : n ≠ 0) :
    0 ≤ Int.fdiv (n.bitLength - 1) 2 :=
  Int.fdiv_nonneg (by have := Int.bitLength_pos hn; omega) (by omega)

/-- Initial size condition holds for `c = ⌊(n.bitLength - 1) / 2⌋`. -/
theorem size_condition_initial {n : Int} (hn : 0 < n) :
    hasSizeCondition n (Int.fdiv (n.bitLength - 1) 2) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
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
  obtain ⟨h_lo, h_hi⟩ := size_condition_initial_nat hm_pos
  refine hasSizeCondition_of_toNat (isqrt_c_nonneg (by exact_mod_cast hm_pos.ne')) ?_ ?_
  · rw [h_toNat]; exact_mod_cast h_lo
  · rw [h_toNat]; exact_mod_cast h_hi

/-- Size condition preserved by the recursive step: `c ↦ ⌊c/2⌋`, `n ↦ ⌊n / 4M²⌋` where the
step's scaler is `M = 2^⌊(c-1)/2⌋`. The `4M²` denominator is the Python shift `2^(2⌊(c-1)/2⌋+2)`
the recursion divides by, written in the form `key_isqrt_lemma` consumes. -/
theorem size_condition_step {n c M : Int} (hM : M = 2 ^ (Int.fdiv (c - 1) 2).toNat)
    (hc : 0 < c) (h : hasSizeCondition n c) :
    hasSizeCondition (Int.fdiv n (4 * M ^ 2)) (Int.fdiv c 2) := by
  -- Read the `4M²` denominator as the Python shift `2^(2k+2)`, then descend in shift form.
  have hk_nn : (0 : Int) ≤ Int.fdiv (c - 1) 2 := Int.fdiv_nonneg (by linarith) (by norm_num)
  rw [hM, four_mul_two_pow_sq hk_nn]
  obtain ⟨nn, rfl⟩ := Int.eq_ofNat_of_zero_le h.nonneg
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc.le
  have hcn_pos : 0 < cn := by exact_mod_cast hc
  obtain ⟨h_lo_nat, h_hi_nat⟩ := hasSizeCondition_natCast_iff.mp h
  -- ⌊cn / 2⌋.toNat = cn / 2
  have h_c2 : (Int.fdiv (↑cn : Int) 2).toNat = cn / 2 := by
    rw [show ((2 : Int)) = ((2 : Nat) : Int) from rfl,
        Int.toNat_fdiv_of_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)]
    simp
  -- ⌊(cn - 1) / 2⌋.toNat = (cn - 1) / 2
  have h_c12 : (Int.fdiv (↑cn - 1 : Int) 2).toNat = (cn - 1) / 2 :=
    Int.toNat_fdiv_pred_two hcn_pos
  -- The shifted value equals the Int-cast of the Nat-level shifted value.
  have h_shift :
      Int.fdiv (↑nn : Int) (2 ^ (2 * Int.fdiv (↑cn - 1 : Int) 2 + 2).toNat)
        = ((nn / 2 ^ (2 * ((cn - 1) / 2) + 2) : Nat) : Int) := by
    have h_shamt : (2 * Int.fdiv (↑cn - 1 : Int) 2 + 2).toNat
                  = 2 * ((cn - 1) / 2) + 2 := by
      have h_k_nn : 0 ≤ Int.fdiv (↑cn - 1 : Int) 2 :=
        Int.fdiv_nonneg (by have : (1:Int) ≤ cn := by exact_mod_cast hcn_pos
                            linarith) (by norm_num)
      rw [← h_c12]; omega
    rw [h_shamt,
        show ((2 : Int) ^ (2 * ((cn - 1) / 2) + 2))
              = ((2 ^ (2 * ((cn - 1) / 2) + 2) : Nat) : Int) by push_cast; rfl,
        Int.fdiv_natCast_natCast]
  obtain ⟨step_lo, step_hi⟩ := size_condition_step_nat hcn_pos h_lo_nat h_hi_nat
  -- Assemble the Int-level conclusion.
  refine hasSizeCondition_of_toNat (Int.fdiv_nonneg (by positivity) (by norm_num)) ?_ ?_
  · rw [h_c2, h_shift]; exact_mod_cast step_lo
  · rw [h_c2, h_shift]; exact_mod_cast step_hi

/-- `4 * M^4 ≤ n` from the size condition, where `M = 2^⌊(c-1)/2⌋.toNat`. -/
theorem M_bound_from_size {n c : Int} (hc : 0 < c) (h : hasSizeCondition n c) :
    4 * ((2 : Int) ^ ((Int.fdiv (c - 1) 2).toNat)) ^ 4 ≤ n := by
  obtain ⟨nn, rfl⟩ := Int.eq_ofNat_of_zero_le h.nonneg
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le hc.le
  have hcn_pos : 0 < cn := by exact_mod_cast hc
  obtain ⟨h_lo_nat, _⟩ := hasSizeCondition_natCast_iff.mp h
  rw [Int.toNat_fdiv_pred_two hcn_pos]
  exact_mod_cast M_bound_from_size_nat hcn_pos h_lo_nat

/-- A suitable scaler from the size condition: for `0 < c` with `4^c ≤ n < 4^(c+1)`, the step's
scaler `M = 2^⌊(c-1)/2⌋` is suitable for `n` — positivity is immediate, and the `4M⁴ ≤ n` bound
is `M_bound_from_size`. This is the form the key lemma consumes. -/
theorem isSuitableScaler_of_hasSizeCondition {n c M : Int}
    (hM : M = 2 ^ (Int.fdiv (c - 1) 2).toNat) (hc : 0 < c) (h : hasSizeCondition n c) :
    isSuitableScaler n M := by
  subst hM
  exact ⟨by positivity, M_bound_from_size hc h⟩

/-- Base case of the recursion: at `c = 0` the size condition `1 ≤ n < 4` makes `1` a near
square root of `n`. The counterpart to the step-case bridge
`isSuitableScaler_of_hasSizeCondition`. -/
theorem isNearSquareRoot_one_of_hasSizeCondition {n : Int} (h : hasSizeCondition n 0) :
    isNearSquareRoot n 1 := by
  obtain ⟨h_lo, h_hi⟩ := h
  simp only [Int.toNat_zero, Int.toNat_one, zero_add, pow_zero, pow_one] at h_lo h_hi
  exact ⟨by show (1 - 1) * (1 - 1) < n; omega, by show n < (1 + 1) * (1 + 1); omega⟩

/-! ## Size condition at depth -/

/-- The value `⌊n / 4^(c-d)⌋` at depth `d` (`0 ≤ d ≤ c`) inherits the size condition from
`hasSizeCondition n c`, now at level `d`. The construction proof behind `SizedProblem.subAt`, and
the `(n,c)`-only fact the seed and step of both loop invariants lean on. -/
theorem size_condition_at_depth {n c d : Int} (hd_lo : 0 ≤ d) (hd_hi : d ≤ c)
    (h : hasSizeCondition n c) :
    hasSizeCondition (n.fdiv (4 ^ (c - d).toNat)) d := by
  obtain ⟨nn, rfl⟩ := Int.eq_ofNat_of_zero_le h.nonneg
  obtain ⟨cn, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans hd_lo hd_hi)
  obtain ⟨dn, rfl⟩ := Int.eq_ofNat_of_zero_le hd_lo
  have hdN : (↑dn : Int).toNat = dn := Int.toNat_natCast dn
  have hdc : dn ≤ cn := by exact_mod_cast hd_hi
  -- (c - d).toNat = cn - dn
  have h_cd : ((↑cn - ↑dn : Int)).toNat = cn - dn := by
    rw [show ((↑cn : Int) - ↑dn) = ((cn - dn : Nat) : Int) from (Nat.cast_sub hdc).symm]
    exact Int.toNat_natCast _
  -- The fdiv of nonneg-nat casts is the natCast of the Nat division.
  have h_bridge : Int.fdiv (↑nn : Int) ((4 : Int) ^ (cn - dn))
                    = ((nn / 4 ^ (cn - dn) : Nat) : Int) := by
    rw [show ((4 : Int) ^ (cn - dn)) = ((4 ^ (cn - dn) : Nat) : Int) from by push_cast; rfl,
        Int.fdiv_natCast_natCast]
  obtain ⟨h_lo_nat, h_hi_nat⟩ := hasSizeCondition_natCast_iff.mp h
  obtain ⟨step_lo, step_hi⟩ := size_condition_at_depth_nat hdc h_lo_nat h_hi_nat
  -- Assemble the Int-level conclusion.
  refine hasSizeCondition_of_toNat (by positivity) ?_ ?_
  · rw [hdN, h_cd, h_bridge]; exact_mod_cast step_lo
  · rw [hdN, h_cd, h_bridge]; exact_mod_cast step_hi

end
