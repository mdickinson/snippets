/-
The `SizedProblem` algebra: the problem instance both correctness proofs operate on, and the
operations they are phrased in — all in the algorithm's native language of shifts and bit lengths.

A `SizedProblem` bundles a value `n`, a recursion level `c`, and the size invariant `isSizedAt n c`
(`0 < n ∧ c = ⌊log₂ n / 2⌋`, the bit-length form). `descend` is one reduction step
`(n, c) ↦ (n >>> (2·shift+2), ⌊c/2⌋)`; `newtonLift` lifts a near square root of the descended
problem back to one for the original, as `(a << shift) + ⌊(n >> shift+2) / a⌋`.
`isNearSquareRoot_newtonLift` is the single mathematical step both proofs share — there the shift
form crosses to `key_isqrt_lemma`'s multiplicative `Ma + ⌊n / 4Ma⌋`.

The two proofs walk the same chain of sized problems by these operations. The recursion solves
`p.descend` and lifts. The iterative loop climbs the chain `p.subAt d` of depth-`d` subproblems
(`subAt 0` the base, `subAt p.c = p` the whole problem); `descend_subAt` makes each loop step the
reverse of a single `descend`, and `subAt_body_eq` decodes the loop body to a `newtonLift`.

`shift = shifter p = ⌊(c-1)/2⌋` is the shared shift amount; `scaler = 2^shift = M` is the
multiplicative scaler the key lemma reads. The size-condition theory (`size_condition_step`,
`size_condition_at_depth`, the power-bound bridge behind `hsc`) comes from `SizeConditions`; the
shift↔`fdiv` value bridge (`Int.shiftRight_eq_fdiv`) from `FDivLemmas`; the `4M²`/`4Ma` scaler
identity (`key_isqrt_body_eq`) from `PythonPrimitivesLemmas`.
-/

module

public import Isqrt.Definitions.Specification
public import Isqrt.Proofs.SizeConditions
import Isqrt.Proofs.KeyLemma
import Isqrt.Proofs.PythonPrimitivesLemmas
import Isqrt.Proofs.FDivLemmas

public section

/-- A *sized problem*: a value `n`, a recursion level `c`, and the size invariant `isSizedAt n c`
(`0 < n ∧ c = ⌊log₂ n / 2⌋`) relating them. The unit the correctness recursion operates on, and the
vocabulary `descend` / `newtonLift` are stated in. The invariant is carried in its bit-length form
so instances are built in the same shift/bit-length language; the power bound `4^c ≤ n < 4^(c+1)`
the key lemma wants is the derived `hsc`. -/
structure SizedProblem where
  /-- The value whose near square root is sought (at this recursion level). -/
  n : Int
  /-- The recursion level. -/
  c : Nat
  /-- The size invariant `isSizedAt n c` in bit-length form. -/
  hsize : isSizedAt n c

namespace SizedProblem

/-- Two sized problems are equal when their value and level agree — the size invariant `hsize` is
proof-irrelevant, so it need not be compared. -/
theorem ext {p q : SizedProblem} (hn : p.n = q.n) (hc : p.c = q.c) : p = q := by
  cases p; cases q; subst hn; subst hc; rfl

/-- The power bound `4^c ≤ n < 4^(c+1)`, derived from the bit-length field `hsize`
(`hasSizeCondition_of_isSizedAt`). The form the key lemma consumes; exposed as `.hsc` so the
correctness proofs and `isNearSquareRoot_newtonLift` read the power bound directly off a problem. -/
theorem hsc (p : SizedProblem) : hasSizeCondition p.n p.c :=
  hasSizeCondition_of_isSizedAt p.hsize

/-- The step shift amount `shift = ⌊(c-1)/2⌋`: `descend` right-shifts by `2·shift+2`, `newtonLift`
left-shifts `a` by `shift`. Total: at `c = 0` the `Nat` subtraction `c - 1` truncates to `0`,
giving shift `0` — harmless, since every fact that gives it meaning takes `0 < c`. -/
@[expose] def shifter (p : SizedProblem) : Nat := (p.c - 1) / 2

/-- The step scaler `M = 2^shift`, the multiplicative form of the shift the key lemma reads:
`newtonLift`'s `a << shift` is `Ma` and its `n >> shift+2` divides by `4M`. Never `0`, and every
fact that gives it meaning takes `0 < c`. `descend` and `newtonLift` read their shift from
`shifter`, so they agree by definition. -/
@[expose] def scaler (p : SizedProblem) : Int := 2 ^ p.shifter

/-- One reduction step: `(n, c) ↦ (n >>> (2·shift+2), ⌊c/2⌋)`, carrying the size invariant down to
the child (`size_condition_step`). The right-shift by `2·shift+2` is the algorithm's division by
the step's `4M²`; `hc : 0 < p.c` feeds only the child's invariant, so the value field reduces
without it. -/
@[expose] def descend (p : SizedProblem) (hc : 0 < p.c) : SizedProblem :=
  ⟨p.n >>> (2 * p.shifter + 2), p.c / 2, by
    rw [Int.shiftRight_eq_fdiv]; exact size_condition_step hc p.hsize⟩

/-- The Newton combine: lift a value `a` for the descended problem back to one for `p`, as
`(a << shift) + ⌊(n >> shift+2) / a⌋` — a left shift of `a` (the `Ma` term) plus the divided-down
remainder. Paired with `descend` through the shared `shifter`; `isNearSquareRoot_newtonLift` is the
fact that it carries a near square root to a near square root, crossing to the key lemma's
`Ma + ⌊n / 4Ma⌋` there. -/
@[expose] def newtonLift (p : SizedProblem) (a : Int) : Int :=
  (a <<< p.shifter) + (p.n >>> (p.shifter + 2)).fdiv a

/-- The depth-`d` subproblem of `p` as a sized problem: the value `p.n >>> 2(c-d)` (right-shift by
the depth-`d` shift) paired with level `d` and the inherited size invariant
(`size_condition_at_depth`), for `d ≤ p.c`. This is the vocabulary the iterative loop's invariant
is phrased in — the loop walks the chain `p.subAt 0` (the base) up to `p.subAt p.c = p` (the whole
problem). -/
@[expose] def subAt (p : SizedProblem) (d : Nat) (hhi : d ≤ p.c) : SizedProblem :=
  ⟨p.n >>> (2 * (p.c - d)), d, by
    rw [Int.shiftRight_eq_fdiv]; exact size_condition_at_depth hhi p.hsize⟩

/-- Descending the depth-`d` subproblem gives the depth-`⌊d/2⌋` subproblem:
`descend (p.subAt d) = p.subAt ⌊d/2⌋`. The value field is the shift identity that composing the
subproblem's shift `2(c-d)` with the step's `2·⌊(d-1)/2⌋+2` lands on the depth-`⌊d/2⌋` shift
`2(c - ⌊d/2⌋)` — pure shift-amount bookkeeping (`omega`) once the two right-shifts collapse; the
level field is `rfl`. This is what makes one loop iteration the reverse of a single `descend`, so
the loop and the recursion walk the same chain. -/
theorem descend_subAt {p : SizedProblem} {d : Nat} (hhi : d ≤ p.c) (hd_pos : 0 < d) :
    (p.subAt d hhi).descend hd_pos
      = p.subAt (d >>> 1) (Nat.le_trans (Nat.shiftRight_le d 1) hhi) := by
  apply SizedProblem.ext
  · show (p.n >>> (2 * (p.c - d))) >>> (2 * ((d - 1) / 2) + 2) = p.n >>> (2 * (p.c - d / 2))
    rw [← Int.shiftRight_add,
        show 2 * (p.c - d) + (2 * ((d - 1) / 2) + 2) = 2 * (p.c - d / 2) from by omega]
  · rfl

/-- The iterative loop body, decoded, is the Newton lift of the depth-`d` subproblem `p.subAt d`.
With the threaded child shift `e = ⌊d/2⌋` (`0 < d`), the body value
`(a << d-e-1) + ⌊(p.n >> 2c-e-d+1) / a⌋` equals `(p.subAt d).newtonLift a`. Both sides are shifts:
composing the lift's two right-shifts (`Int.shiftRight_add`), the flat shift `2c-e-d+1` and the
split shift `2(c-d) + (⌊(d-1)/2⌋+2)` agree by `omega`, as do the left-shift amounts `d-e-1` and
`⌊(d-1)/2⌋`. -/
theorem subAt_body_eq {p : SizedProblem} {d e : Nat} {a : Int} (hhi : d ≤ p.c)
    (he : e = d >>> 1) (hd_pos : 0 < d) :
    a <<< (d - e - 1) + Int.fdiv (p.n >>> (2 * p.c - e - d + 1)) a
      = (p.subAt d hhi).newtonLift a := by
  -- `d >>> 1` is `d / 2`; restate the child shift so the arithmetic below reads the division.
  have he : e = d / 2 := he
  show a <<< (d - e - 1) + (p.n >>> (2 * p.c - e - d + 1)).fdiv a
      = a <<< ((d - 1) / 2) + ((p.n >>> (2 * (p.c - d))) >>> ((d - 1) / 2 + 2)).fdiv a
  rw [← Int.shiftRight_add,
      show d - e - 1 = (d - 1) / 2 from by omega,
      show 2 * p.c - e - d + 1 = 2 * (p.c - d) + ((d - 1) / 2 + 2) from by omega]

/-! ### Crossings to the key lemma's multiplicative form

The two places `SizedProblem`'s shift vocabulary meets `key_isqrt_lemma`'s `M`/`4M²`/`4Ma`. Both
correctness proofs route through these, so the shift↔multiplicative crossing lives here, not smeared
across the proofs. -/

/-- The descended value `n >> (2·shift+2)` is the key lemma's `⌊n / 4M²⌋` (`M = scaler = 2^shift`):
the right-shift by `2·shift+2` is division by `2^(2·shift+2) = 4M²` (`four_mul_two_pow_sq`). -/
theorem descend_n_eq (p : SizedProblem) (hc : 0 < p.c) :
    (p.descend hc).n = p.n.fdiv (4 * p.scaler ^ 2) := by
  show p.n >>> (2 * p.shifter + 2) = p.n.fdiv (4 * p.scaler ^ 2)
  rw [Int.shiftRight_eq_fdiv,
    show (4 : Int) * p.scaler ^ 2 = 2 ^ (2 * p.shifter + 2) from four_mul_two_pow_sq p.shifter]

/-- `newtonLift` in the key lemma's multiplicative form, for `0 < a`:
`(a << shift) + ⌊(n >> shift+2) / a⌋ = Ma + ⌊n / 4Ma⌋` (`M = scaler = 2^shift`). The left shift is
`Ma` and the inner right-shift divides by `4M` (`key_isqrt_body_eq`). -/
theorem newtonLift_eq (p : SizedProblem) {a : Int} (ha : 0 < a) :
    p.newtonLift a = p.scaler * a + p.n.fdiv (4 * p.scaler * a) := by
  show (a <<< p.shifter) + (p.n >>> (p.shifter + 2)).fdiv a
      = p.scaler * a + p.n.fdiv (4 * p.scaler * a)
  rw [Int.shiftLeft_eq, Int.shiftRight_eq_fdiv]
  exact key_isqrt_body_eq ha rfl

end SizedProblem

/-- The Newton refinement step on `SizedProblem`s: a near square root of the descended problem lifts
to one of `p`. This is `key_isqrt_lemma` repackaged — the single mathematical step the correctness
proofs share (the recursion applies it at the top, the loop at each revealed level). The shift form
of `newtonLift` crosses to the key lemma's multiplicative `Ma + ⌊n / 4Ma⌋` here, through
`key_isqrt_body_eq`. -/
theorem isNearSquareRoot_newtonLift {p : SizedProblem} (hc : 0 < p.c) {a : Int}
    (h : isNearSquareRoot (p.descend hc).n a) : isNearSquareRoot p.n (p.newtonLift a) := by
  have hscaler : isSuitableScaler p.n p.scaler :=
    isSuitableScaler_of_hasSizeCondition rfl hc p.hsc
  rw [p.descend_n_eq hc] at h
  rw [p.newtonLift_eq h.pos]
  exact key_isqrt_lemma hscaler h

end
