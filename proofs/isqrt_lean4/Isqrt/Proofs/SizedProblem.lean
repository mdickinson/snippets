/-
The `SizedProblem` algebra: the problem instance both correctness proofs operate on, and the
operations they are phrased in.

A `SizedProblem` bundles a value `n`, a recursion level `c`, and the size invariant
`hasSizeCondition n c` (`4^c ≤ n < 4^(c+1)`). `descend` is one reduction step
`(n, c) ↦ (⌊n / 4M²⌋, ⌊c/2⌋)`; `newtonLift` lifts a near square root of the descended problem back
to one for the original, as `Ma + ⌊n / 4Ma⌋`. `isNearSquareRoot_newtonLift` is the single
mathematical step both proofs share (`key_isqrt_lemma` repackaged).

The two proofs walk the same chain of sized problems by these operations. The recursion solves
`p.descend` and lifts. The iterative loop climbs the chain `p.subAt d` of depth-`d` subproblems
(`subAt 0` the base, `subAt p.c = p` the whole problem); `descend_subAt` makes each loop step the
reverse of a single `descend`, and `subAt_body_eq` decodes the loop body to a `newtonLift`.

`M = scaler p = 2^⌊(c-1)/2⌋` is the shared step scaler: `descend` divides by `4M²`, `newtonLift`
multiplies by `M`. The Python shift encoding stays out, in the two correctness proofs. The
size-condition theory (`size_condition_step`, `size_condition_at_depth`) comes from `SizeConditions`;
the bit-level identities (`four_mul_two_pow_sq`, `key_isqrt_body_eq`) from `PythonPrimitivesLemmas`.
-/

module

public import Isqrt.Definitions.Specification
public import Isqrt.Proofs.SizeConditions
import Isqrt.Proofs.KeyLemma
import Isqrt.Proofs.PythonPrimitivesLemmas
import Isqrt.Proofs.FDivLemmas

public section

/-- A *sized problem*: a value `n`, a recursion level `c`, and the size invariant
`4^c ≤ n < 4^(c+1)` (`hasSizeCondition n c`) relating them. The unit the correctness recursion
operates on, and the vocabulary `descend` / `newtonLift` are stated in. -/
structure SizedProblem where
  /-- The value whose near square root is sought (at this recursion level). -/
  n : Int
  /-- The recursion level. -/
  c : Nat
  /-- The size invariant `4^c ≤ n < 4^(c+1)`. -/
  hsc : hasSizeCondition n c

namespace SizedProblem

/-- Two sized problems are equal when their value and level agree — the size invariant `hsc` is
proof-irrelevant, so it need not be compared. -/
theorem ext {p q : SizedProblem} (hn : p.n = q.n) (hc : p.c = q.c) : p = q := by
  cases p; cases q; subst hn; subst hc; rfl

/-- The step scaler `M = 2^⌊(c-1)/2⌋`. Total: at `c = 0` the `Nat` subtraction `c - 1` truncates to
`0`, giving exponent `0` and `M = 1` — harmless, since `M` is never `0` and every fact that gives it
meaning takes `0 < c`. `descend` and `newtonLift` both read their `M` from here, so they agree by
definition. -/
@[expose] def scaler (p : SizedProblem) : Int := 2 ^ ((p.c - 1) / 2)

/-- One reduction step: `(n, c) ↦ (⌊n / 4M²⌋, ⌊c/2⌋)`, carrying the size invariant down to the
child (`size_condition_step`). The divisor `4M²` is the form the algorithm and `key_isqrt_lemma`
divide by; `hc : 0 < p.c` feeds only the child's invariant, so the value fields reduce without it. -/
@[expose] def descend (p : SizedProblem) (hc : 0 < p.c) : SizedProblem :=
  ⟨p.n.fdiv (4 * p.scaler ^ 2), p.c / 2, size_condition_step rfl hc p.hsc⟩

/-- The Newton combine: lift a value `a` for the descended problem back to one for `p`, as
`Ma + ⌊n / 4Ma⌋`. Paired with `descend` through the shared `scaler`; `isNearSquareRoot_newtonLift`
is the fact that it carries a near square root to a near square root. -/
@[expose] def newtonLift (p : SizedProblem) (a : Int) : Int :=
  p.scaler * a + p.n.fdiv (4 * p.scaler * a)

/-- The depth-`d` subproblem of `p` as a sized problem: the value `⌊p.n / 4^(p.c-d)⌋` paired with
level `d` and the inherited size invariant (`size_condition_at_depth`), for `d ≤ p.c`. This is
the vocabulary the iterative loop's invariant is phrased in — the loop walks the chain
`p.subAt 0` (the base) up to `p.subAt p.c = p` (the whole problem). -/
@[expose] def subAt (p : SizedProblem) (d : Nat) (hhi : d ≤ p.c) : SizedProblem :=
  ⟨p.n.fdiv (4 ^ (p.c - d)), d, size_condition_at_depth hhi p.hsc⟩

/-- Descending the depth-`d` subproblem gives the depth-`⌊d/2⌋` subproblem:
`descend (p.subAt d) = p.subAt ⌊d/2⌋`. The value field is the base-4 identity that the step's
divisor `4M²` (for `M = 2^⌊(d-1)/2⌋`) bridges depths `d` and `⌊d/2⌋`; the level field is `rfl`. This
is what makes one loop iteration the reverse of a single `descend`, so the loop and the recursion
walk the same chain. -/
theorem descend_subAt {p : SizedProblem} {d : Nat} (hhi : d ≤ p.c) (hd_pos : 0 < d) :
    (p.subAt d hhi).descend hd_pos
      = p.subAt (d / 2) (Nat.le_trans (Nat.div_le_self d 2) hhi) := by
  apply SizedProblem.ext
  · show (p.n.fdiv (4 ^ (p.c - d))).fdiv (4 * (2 ^ ((d - 1) / 2)) ^ 2)
        = p.n.fdiv (4 ^ (p.c - d / 2))
    rw [four_mul_two_pow_sq ((d - 1) / 2),
        Int.fdiv_fdiv_eq_fdiv_mul p.n (Int.pow_nonneg (by omega)) (Int.pow_nonneg (by omega))]
    congr 1
    rw [show (4 : Int) = 2 ^ 2 by decide]
    simp only [← Int.pow_mul, ← Int.pow_add]
    congr 1
    omega
  · rfl

/-- At full depth the subproblem is the whole problem: `p.subAt p.c = p`. -/
theorem subAt_self (p : SizedProblem) : p.subAt p.c (Nat.le_refl _) = p := by
  apply SizedProblem.ext
  · show p.n.fdiv (4 ^ (p.c - p.c)) = p.n
    simp only [Nat.sub_self, Int.pow_zero, Int.fdiv_one]
  · rfl

/-- The iterative loop body, decoded, is the Newton lift of the depth-`d` subproblem `p.subAt d`.
With the threaded child shift `e = ⌊d/2⌋` (`0 < d`, `0 < a`), the body value
`a·2^(d-e-1) + ⌊⌊p.n / 2^(2c-e-d+1)⌋ / a⌋` equals `(p.subAt d).newtonLift a`. The work beyond
`key_isqrt_body_eq` is undoing the loop's encoding of depth as `c >> s`: the flat shift
`2^(2c-e-d+1)` splits into the subproblem's `4^(c-d)` and the key lemma's `2^(⌊(d-1)/2⌋+2)`. -/
theorem subAt_body_eq {p : SizedProblem} {d e : Nat} {a : Int} (hhi : d ≤ p.c)
    (he : e = d / 2) (hd_pos : 0 < d) (ha : 0 < a) :
    a * 2 ^ (d - e - 1)
        + Int.fdiv (Int.fdiv p.n (2 ^ (2 * p.c - e - d + 1))) a
      = (p.subAt d hhi).newtonLift a := by
  show a * 2 ^ (d - e - 1)
      + Int.fdiv (Int.fdiv p.n (2 ^ (2 * p.c - e - d + 1))) a
    = 2 ^ ((d - 1) / 2) * a
      + (p.n.fdiv (4 ^ (p.c - d))).fdiv (4 * 2 ^ ((d - 1) / 2) * a)
  have hk_eq : (d - 1) / 2 = d - e - 1 := by rw [he]; omega
  -- split the flat shift into the subproblem's `4^(c-d)` and the key lemma's `2^(k+2)`
  have hbridge : Int.fdiv p.n (2 ^ (2 * p.c - e - d + 1))
      = (p.n.fdiv (4 ^ (p.c - d))).fdiv (2 ^ ((d - 1) / 2 + 2)) := by
    rw [Int.fdiv_fdiv_eq_fdiv_mul p.n (Int.pow_nonneg (by omega)) (Int.pow_nonneg (by omega))]
    congr 1
    rw [show (4 : Int) = 2 ^ 2 by decide]
    simp only [← Int.pow_mul, ← Int.pow_add]
    congr 1
    omega
  rw [show (d - e - 1) = (d - 1) / 2 from hk_eq.symm, hbridge]
  exact key_isqrt_body_eq ha rfl

end SizedProblem

/-- The Newton refinement step on `SizedProblem`s: a near square root of the descended problem lifts
to one of `p`. This is `key_isqrt_lemma` repackaged — the single mathematical step the correctness
proofs share (the recursion applies it at the top, the loop at each revealed level). -/
theorem isNearSquareRoot_newtonLift {p : SizedProblem} (hc : 0 < p.c) {a : Int}
    (h : isNearSquareRoot (p.descend hc).n a) : isNearSquareRoot p.n (p.newtonLift a) := by
  have hscaler : isSuitableScaler p.n p.scaler :=
    isSuitableScaler_of_hasSizeCondition rfl hc p.hsc
  exact key_isqrt_lemma hscaler h

end
