/-
The bit-level theory the correctness proofs consume, all stated in pure `Int.fdiv` /
`2 ^ ·` form (no Python operators) so the proofs build on them directly. Three groups.
(The pure-integer mathematics — near-square-root theory and the Newton-step key lemma —
lives in `Isqrt.Proofs.KeyLemma`.)

**Value extraction.** On its non-raising branch `pyFloordiv` returns `.ok` of the `Int.fdiv`,
and `pyLshift` / `pyRshift` return `.ok` of the native shift `· <<< ·` / `· >>> ·`. The `_eq_ok`
lemmas (with `Except.ok_bind`) are the bridges the proofs use to step through the `do`-block once
the side conditions (nonzero divisor, nonneg shift) are discharged; the shift forms keep the proofs
in shift vocabulary until the key-lemma seam.

**Bit length.** The power-of-two facts about `int.bit_length()`. The public `Int.bitLength`
inlines its bit-length computation; this file re-declares it as the Nat-level `natBitLength`
— kept honest by `Int.bitLength_natCast` — and connects it, via `Nat.log2`, to the
power-of-two bounds the size-condition and loop-depth proofs consume.

**Scaler encoding.** The shift exponents the algorithm divides by are the key lemma's
`4M²` / `4Ma` denominators for the scaler `M = 2^k`: `four_mul_two_pow_sq` and
`key_isqrt_body_eq` are the bridges that let both correctness proofs read a shift as
division by the scaler.
-/

module

public import Isqrt.Definitions.PythonPrimitives
import Isqrt.Proofs.SupportLemmas

public section

/-! ## Value extraction: the `Except`-returning operations -/

/-- For a nonzero divisor, `pyFloordiv` takes its `.ok` branch. -/
theorem pyFloordiv_eq_ok {a b : Int} (hb : b ≠ 0) :
    pyFloordiv a b = .ok (Int.fdiv a b) := by
  unfold pyFloordiv; split
  · omega
  · rfl

/-- For a nonneg shift count, `pyLshift` takes its `.ok` branch, returning the native left shift
`· <<< ·`. The shift-form value flows directly into the proofs (`Int.shiftLeft_eq` converts it to
`· * 2^·` only at the key-lemma seam). -/
theorem pyLshift_eq_ok {n k : Int} (hk : 0 ≤ k) :
    pyLshift n k = .ok (n <<< k.toNat) := by
  unfold pyLshift; split
  · omega
  · rfl

/-- For a nonneg shift count, `pyRshift` takes its `.ok` branch, returning the native arithmetic
right shift `· >>> ·`. The shift-form value flows directly into the proofs (`Int.shiftRight_eq_fdiv`
converts it to `Int.fdiv · (2^·)` only at the seam). -/
theorem pyRshift_eq_ok {n k : Int} (hk : 0 ≤ k) :
    pyRshift n k = .ok (n >>> k.toNat) := by
  unfold pyRshift; split
  · omega
  · rfl

/-- `Except.ok a >>= f = f a` (definitional). The companion to the `_eq_ok`
lemmas above: once one of them rewrites an operation to `.ok v`, this steps the
`do`-block past the resulting bind. It's the `.ok`-form analogue of `pure_bind`,
which `simp` won't fire on a literal `Except.ok` (the head it sees is `Except.ok`,
not `pure`). Both correctness proofs use it. -/
theorem Except.ok_bind {ε α β : Type _} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-! ## natBitLength: the Nat-level bit length -/

/-- Bit length of a natural number: the number of bits needed to represent `n`,
with `natBitLength 0 = 0`. Equivalent to `Nat.size`; defined via `Nat.log2` for
access to core Lean 4's `log2` lemma library.

This is the Nat-level workhorse the bit-length proofs run on. It is *not* trust
surface: the public `Int.bitLength` (`Isqrt.Definitions.PythonPrimitives`) computes the same
bit length, and `Int.bitLength_natCast` below verifies — by a one-line `cases` — that
the two agree, so this re-declaration cannot silently drift from it. -/
def natBitLength (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-! ## Int.bitLength: defining-equation lemmas -/

/-- `Int.bitLength` of a `Nat`-cast drops the `natAbs`: `(↑m : Int).bitLength = ↑(natBitLength m)`.
This is the bridge tying the trust-surface `Int.bitLength` to the named `natBitLength` above:
`cases m <;> rfl` checks they agree on each constructor — splitting `m` lets the `n = 0`
conditional reduce — so the re-declaration cannot silently drift. It's also the
form the Int↔Nat bridges below (and in `Isqrt.Proofs.SizeConditions`) `rw` with directly;
the general `Int.bitLength_def` is the `@[simp]` normal form, so this one isn't `@[simp]`. -/
theorem Int.bitLength_natCast (m : Nat) : (↑m : Int).bitLength = ↑(natBitLength m) := by
  cases m <;> rfl

/-- `Int.bitLength` unfolds to `natBitLength` on the underlying `natAbs`. Generalises
`Int.bitLength_natCast` from a `Nat`-cast to any `n : Int`: both sides depend on `n` only
through `n.natAbs` (and `Int.bitLength`'s `n = 0` guard agrees with `n.natAbs = 0`). -/
@[simp]
theorem Int.bitLength_def (n : Int) : n.bitLength = ↑(natBitLength n.natAbs) := by
  rw [← Int.bitLength_natCast]
  unfold Int.bitLength
  simp

/-- `.toNat` of `Int.bitLength_natCast`: `((↑m : Int).bitLength).toNat = natBitLength m`. Not
`@[simp]` (simp derives it from `Int.bitLength_def` + casts); kept as a named target for
the *targeted* `rw`s below that must not disturb neighbouring casts. -/
theorem Int.toNat_bitLength_natCast (m : Nat) :
    ((↑m : Int).bitLength).toNat = natBitLength m := by
  rw [Int.bitLength_natCast, Int.toNat_natCast]

/-! ## natBitLength: basic properties -/

theorem natBitLength_eq_zero_iff {n : Nat} : natBitLength n = 0 ↔ n = 0 := by
  by_cases h : n = 0 <;> simp [natBitLength, h]

theorem natBitLength_pos_iff {n : Nat} : 0 < natBitLength n ↔ 0 < n := by
  rw [Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero]
  exact not_congr natBitLength_eq_zero_iff

/-! ## natBitLength: power-of-two bounds -/

/-- Upper bound: `n < 2 ^ (natBitLength n)` for all `n`. -/
theorem lt_two_pow_natBitLength (n : Nat) : n < 2 ^ natBitLength n := by
  by_cases h : n = 0
  · subst h; simp [natBitLength]
  · simp only [natBitLength, if_neg h]; exact Nat.lt_log2_self

/-- Lower bound: `2 ^ (natBitLength n - 1) ≤ n` when `n > 0`. -/
theorem two_pow_pred_natBitLength_le {n : Nat} (hn : 0 < n) :
    2 ^ (natBitLength n - 1) ≤ n := by
  simp only [natBitLength, if_neg (by omega : ¬ n = 0), Nat.add_sub_cancel]
  exact Nat.log2_self_le (by omega)

/-! ## natBitLength: iff characterizations -/

/-- `natBitLength n ≤ k ↔ n < 2^k`. -/
theorem natBitLength_le_iff {n k : Nat} : natBitLength n ≤ k ↔ n < 2 ^ k := by
  by_cases h : n = 0
  · subst h; exact iff_of_true (Nat.zero_le k) (by apply Nat.pow_pos; decide)
  · simp only [natBitLength, if_neg h, Nat.add_one_le_iff]; exact Nat.log2_lt h

/-- `k < natBitLength n ↔ 2^k ≤ n`. Dual of `natBitLength_le_iff`. -/
theorem lt_natBitLength_iff {n k : Nat} : k < natBitLength n ↔ 2 ^ k ≤ n := by
  have h := @natBitLength_le_iff n k
  omega

/-- `natBitLength n = n.log2 + 1` for `0 < n`, so `natBitLength n - 1 = n.log2`. The
off-by-one between the algorithm's `bit_length` and the proof's `Nat.log2`: the size
condition's seed `(bitLength - 1) / 2` is `log2 / 2`. -/
theorem natBitLength_sub_one {n : Nat} (hn : 0 < n) : natBitLength n - 1 = n.log2 := by
  simp only [natBitLength, if_neg (Nat.ne_of_gt hn), Nat.add_sub_cancel]

/-! ## Int.bitLength: Int-level properties -/

theorem Int.bitLength_nonneg (n : Int) : 0 ≤ n.bitLength := by
  rw [Int.bitLength_def]
  exact Int.natCast_nonneg _

theorem Int.bitLength_eq_zero_iff {n : Int} : n.bitLength = 0 ↔ n = 0 := by
  simp [natBitLength_eq_zero_iff, Int.natAbs_eq_zero]

theorem Int.bitLength_pos {n : Int} (hn : n ≠ 0) : 0 < n.bitLength := by
  have h0 := Int.bitLength_nonneg n
  have hne : n.bitLength ≠ 0 := fun h => hn (Int.bitLength_eq_zero_iff.mp h)
  omega

/-- `⌊(n.bit_length() - 1) / 2⌋` is nonneg for nonzero `n`: `bit_length()` is positive
(`Int.bitLength_pos`), so `bit_length() - 1 ≥ 0` and the floor-division stays nonneg. Lets a
consumer round-trip the value's `.toNat` back through `↑` (`Int.toNat_of_nonneg`). -/
theorem Int.fdiv_bitLength_sub_one_nonneg {n : Int} (hn : n ≠ 0) :
    0 ≤ Int.fdiv (n.bitLength - 1) 2 :=
  Int.fdiv_nonneg (by have := Int.bitLength_pos hn; omega) (by omega)

/-- The algorithm's bit-length seed `⌊(n.bit_length() - 1)/2⌋` equals `n`'s level `⌊log₂ n / 2⌋`.
The `bitLength = log2 + 1` off-by-one (`natBitLength_sub_one`) wrapped in the Int↔Nat casts: the
seam where the Python `(n.bit_length() - 1) // 2` seed meets the size condition's level, so the
correctness proofs can hand the size condition the algorithm's actual seed. -/
theorem Int.toNat_fdiv_bitLength_sub_one {n : Int} (hn : 0 < n) :
    (Int.fdiv (n.bitLength - 1) 2).toNat = n.toNat.log2 / 2 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hn)
  have hm_pos : 0 < m := by exact_mod_cast hn
  have hbl : 1 ≤ natBitLength m := natBitLength_pos_iff.mpr hm_pos
  rw [Int.toNat_natCast, ← natBitLength_sub_one hm_pos, Int.bitLength_natCast,
      show ((natBitLength m : Nat) : Int) - 1 = ((natBitLength m - 1 : Nat) : Int) from by omega,
      show ((2 : Int)) = ((2 : Nat) : Int) from rfl,
      Int.toNat_fdiv_of_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)]
  simp only [Int.toNat_natCast]

/-! ## Scaler encoding: shifts as the key lemma's `4M²` / `4Ma`

The algorithm reduces its input by right-shifting; these identities rewrite those shift
exponents into the `4M²` / `4Ma` scaler form that `Isqrt.Proofs.KeyLemma`'s
`key_isqrt_lemma` consumes, for the scaler `M = 2^k`. -/

/-- The Python right-shift exponent `2k+2` realises the key lemma's `4M²` denominator for the
scaler `M = 2^k`: `4·(2^k)² = 2^(2k+2)`. Lets both correctness proofs read a
`>> (2k+2)` as division by `4M²`. -/
theorem four_mul_two_pow_sq (k : Nat) :
    (4 : Int) * (2 ^ k) ^ 2 = 2 ^ (2 * k + 2) := by
  rw [Int.pow_add, ←Int.pow_mul]; grind only

/-- Bridge from the algorithm's body to `key_isqrt_lemma`'s combining expression.
For `0 < a` and `M = 2^k`, the body value `a·2^k + ⌊⌊ν / 2^(k+2)⌋ / a⌋`
— a left shift of `a` by `k`, plus the divided-down remainder — equals
`Ma + ⌊ν / 4Ma⌋`, the quantity `key_isqrt_lemma` proves is a near square root. Both
correctness proofs apply it to bridge their loop/recursion body to the key lemma: the
recursive proof (`Isqrt.Proofs.RecursiveCorrectness`) with `ν = n`, the iterative proof
(`Isqrt.Proofs.IterativeCorrectness`) with `ν` the depth-shifted `n`. The single algebraic
move is factoring `2^(k+2)` as `4·2^k = 4M`. -/
theorem key_isqrt_body_eq {ν a M : Int} {k : Nat} (ha : 0 < a)
    (hM : M = 2 ^ k) :
    a * 2 ^ k + Int.fdiv (Int.fdiv ν (2 ^ (k + 2))) a
      = M * a + Int.fdiv ν (4 * M * a) := by
  subst hM
  have h_pow : (2 : Int) ^ (k + 2) = 4 * 2 ^ k := by
    rw [Int.pow_add]; grind only
  rw [h_pow, Int.fdiv_fdiv_eq_fdiv_mul ν
      (Int.mul_nonneg (by omega) (Int.pow_nonneg (by omega))) (Int.le_of_lt ha)]
  grind only

end
