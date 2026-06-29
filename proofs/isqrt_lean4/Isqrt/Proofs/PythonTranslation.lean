/-
The bit-level theory the correctness proofs consume, all stated in pure Euclidean division `· / ·`
(`Int.ediv`) / `2 ^ ·` form (no Python operators) so the proofs build on them directly. Three
groups. (The pure-integer mathematics — near-square-root theory and the Newton-step key lemma —
lives in `Isqrt.Proofs.KeyLemma`.)

**Value extraction.** For a positive divisor `pyFloordiv` returns `.ok (a / b)` — its `Int.fdiv`
agrees with `Int.ediv` there, so the bridge hands the proofs the `· / ·` form core's library is
richest in — and `pyLshift` / `pyRshift` return `.ok` of the native shift `· <<< ·` / `· >>> ·`. The
`_eq_ok` lemmas (with `Except.ok_bind`) are the bridges the proofs use to step through the `do`-block
once the side conditions (positive divisor, nonneg shift) are discharged; the shift forms keep the
proofs in shift vocabulary until the key-lemma seam.

**Bit length.** The power-of-two facts about `int.bit_length()`. The public `Int.bitLength` is the
Python `bit_length()` model; these lemmas connect it, via `Nat.log2`, to the power-of-two bounds
the size-condition and loop-depth proofs consume — with the `n = 0` guard discharged at the seam,
since each consumer applies them to a positive argument.

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

/-- For a positive divisor, `pyFloordiv` takes its `.ok` branch, returning the Euclidean quotient
`a / b`: its `Int.fdiv` agrees with `Int.ediv` once the divisor is nonneg
(`Int.fdiv_eq_ediv_of_nonneg`) — the single spot the two divisions are reconciled, so everything
downstream is `· / ·`. -/
theorem pyFloordiv_eq_ok {a b : Int} (hb : 0 < b) :
    pyFloordiv a b = .ok (a / b) := by
  unfold pyFloordiv; split
  · omega
  · rw [Int.fdiv_eq_ediv_of_nonneg a (Int.le_of_lt hb)]; rfl

/-- For a nonneg shift count, `pyLshift` takes its `.ok` branch, returning the native left shift
`· <<< ·`. The shift-form value flows directly into the proofs (`Int.shiftLeft_eq` converts it to
`· * 2^·` only at the key-lemma seam). -/
theorem pyLshift_eq_ok {n k : Int} (hk : 0 ≤ k) :
    pyLshift n k = .ok (n <<< k.toNat) := by
  unfold pyLshift; split
  · omega
  · rfl

/-- For a nonneg shift count, `pyRshift` takes its `.ok` branch, returning the native arithmetic
right shift `· >>> ·`. The shift-form value flows directly into the proofs (`Int.shiftRight_eq_ediv`
converts it to `· / 2^·` only at the seam). -/
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

/-! ## Int.bitLength: relating the trust surface to `Nat.log2`

The public `Int.bitLength` (`Isqrt.Definitions.PythonPrimitives`) is the Python `bit_length()`
model `if n = 0 then 0 else n.natAbs.log2 + 1`. The proofs reason about it through core Lean 4's
`Nat.log2` library. The lone wrinkle is the `n = 0` guard — `Nat.log2 0 + 1 = 1`, not `0` — so the
identification with `log2 + 1` holds only for positive arguments, which is where every consumer
uses it. -/

/-- For positive `m`, `int.bit_length()` is `log2 + 1`: the `n = 0` guard is discharged and
`(↑m).natAbs = m`. The bridge through which the bit-length proofs reach `Nat.log2`. -/
theorem Int.toNat_bitLength_of_pos {m : Nat} (hm : 0 < m) :
    ((↑m : Int).bitLength).toNat = m.log2 + 1 := by
  unfold Int.bitLength
  rw [if_neg (by omega), Int.natAbs_natCast]
  omega

/-- Upper bound `m < 2 ^ bit_length(m)` — the loop-termination fact (`c >> bit_length(c) = 0`).
Holds for all `m`: at `m = 0` the guard gives `bit_length(0) = 0` and `0 < 2 ^ 0`. -/
theorem Int.lt_two_pow_toNat_bitLength (m : Nat) : m < 2 ^ ((↑m : Int).bitLength).toNat := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [Int.bitLength]
  · rw [Int.toNat_bitLength_of_pos h]; exact Nat.lt_log2_self

/-- `0 < bit_length(m) ↔ 0 < m`: the loop's range is nonempty exactly when `m > 0`. -/
theorem Int.toNat_bitLength_pos_iff {m : Nat} : 0 < ((↑m : Int).bitLength).toNat ↔ 0 < m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [Int.bitLength]
  · rw [Int.toNat_bitLength_of_pos h]; omega

/-- `bit_length(m) - 1 = m.log2` for `0 < m`: the off-by-one between the algorithm's `bit_length()`
and the proof's `Nat.log2`, so the seed `(bit_length() - 1) / 2` is `log2 / 2`. -/
theorem Int.toNat_bitLength_sub_one {m : Nat} (hm : 0 < m) :
    ((↑m : Int).bitLength).toNat - 1 = m.log2 := by
  rw [Int.toNat_bitLength_of_pos hm, Nat.add_sub_cancel]

/-- `int.bit_length()` is positive for nonzero `n`: the `n = 0` guard is off, leaving `log2 + 1`. -/
theorem Int.bitLength_pos {n : Int} (hn : n ≠ 0) : 0 < n.bitLength := by
  unfold Int.bitLength; rw [if_neg hn]; omega

/-- `⌊(n.bit_length() - 1) / 2⌋` is nonneg for nonzero `n`: `bit_length()` is positive
(`Int.bitLength_pos`), so `bit_length() - 1 ≥ 0` and the division stays nonneg. Lets a
consumer round-trip the value's `.toNat` back through `↑` (`Int.toNat_of_nonneg`). -/
theorem Int.ediv_bitLength_sub_one_nonneg {n : Int} (hn : n ≠ 0) :
    0 ≤ (n.bitLength - 1) / 2 :=
  Int.ediv_nonneg (by have := Int.bitLength_pos hn; omega) (by omega)

/-- The algorithm's bit-length seed `⌊(n.bit_length() - 1)/2⌋` equals `n`'s level `⌊log₂ n / 2⌋`.
The `bit_length() = log2 + 1` off-by-one wrapped in the Int↔Nat casts: the seam where the Python
`(n.bit_length() - 1) // 2` seed meets the size condition's level, so the correctness proofs can
hand the size condition the algorithm's actual seed. -/
theorem Int.toNat_ediv_bitLength_sub_one {n : Int} (hn : 0 < n) :
    ((n.bitLength - 1) / 2).toNat = n.toNat.log2 / 2 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hn)
  have hm_pos : 0 < m := by exact_mod_cast hn
  have hbl : (↑m : Int).bitLength - 1 = ↑(m.log2) := by
    unfold Int.bitLength
    rw [if_neg (by omega), Int.natAbs_natCast]
    omega
  rw [hbl, Int.toNat_natCast, show ((2 : Int)) = ((2 : Nat) : Int) from rfl,
      ← Int.natCast_ediv, Int.toNat_natCast]

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
For `M = 2^k`, the body value `a·2^k + ⌊⌊ν / 2^(k+2)⌋ / a⌋`
— a left shift of `a` by `k`, plus the divided-down remainder — equals
`Ma + ⌊ν / 4Ma⌋`, the quantity `key_isqrt_lemma` proves is a near square root. Both
correctness proofs apply it to bridge their loop/recursion body to the key lemma: the
recursive proof (`Isqrt.Proofs.RecursiveCorrectness`) with `ν = n`, the iterative proof
(`Isqrt.Proofs.IterativeCorrectness`) with `ν` the depth-shifted `n`. The single algebraic
move is factoring `2^(k+2)` as `4·2^k = 4M`. (Euclidean nesting `⌊⌊ν/y⌋/a⌋ = ⌊ν/(ya)⌋` needs only
`0 ≤ y`, so — unlike the floor-division form — no constraint on `a`.) -/
theorem key_isqrt_body_eq {ν a M : Int} {k : Nat}
    (hM : M = 2 ^ k) :
    a * 2 ^ k + ν / 2 ^ (k + 2) / a
      = M * a + ν / (4 * M * a) := by
  subst hM
  have h_pow : (2 : Int) ^ (k + 2) = 4 * 2 ^ k := by
    rw [Int.pow_add]; grind only
  rw [h_pow, Int.ediv_ediv_of_nonneg
      (Int.mul_nonneg (by omega) (Int.pow_nonneg (by omega)))]
  grind only

end
