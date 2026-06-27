/-
The `SizedProblem` algebra: the problem instance the correctness recursion operates on, plus the
two operations the proofs are phrased in.

A `SizedProblem` bundles a value `n`, a recursion level `c`, and the size invariant
`hasSizeCondition n c` (`4^c ≤ n < 4^(c+1)`). `descend` is one reduction step
`(n, c) ↦ (⌊n / 4M²⌋, ⌊c/2⌋)` carrying the invariant down to the child; `newtonLift` combines a
near square root of the descended problem back into one for the original, as `Ma + ⌊n / 4Ma⌋`. With
these, the recursive correctness proof reads as "solve the descended problem, lift the answer" —
`isNearSquareRoot_newtonLift` is the single mathematical step, `key_isqrt_lemma` repackaged.

`M = scaler p = 2^⌊(c-1)/2⌋` is the shared step scaler: `descend` divides by `4M²`, `newtonLift`
multiplies by `M`. The Python shift encoding and the `4M² ↔ 4^(c-d)` bridge stay out — they live in
`SizeConditions` / `PythonPrimitivesLemmas`.
-/

module

public import Isqrt.Definitions.Specification
public import Isqrt.Proofs.SizeConditions
import Isqrt.Proofs.KeyLemma

public section

/-- A *sized problem*: a value `n`, a recursion level `c`, and the size invariant
`4^c ≤ n < 4^(c+1)` (`hasSizeCondition n c`) relating them. The unit the correctness recursion
operates on, and the vocabulary `descend` / `newtonLift` are stated in. -/
structure SizedProblem where
  /-- The value whose near square root is sought (at this recursion level). -/
  n : Int
  /-- The recursion level. -/
  c : Int
  /-- The size invariant `4^c ≤ n < 4^(c+1)`. -/
  hsc : hasSizeCondition n c

namespace SizedProblem

/-- The step scaler `M = 2^⌊(c-1)/2⌋`. Total: at `c ≤ 0` the `.toNat` clamps the exponent to `0`,
giving `M = 1` — harmless, since `M` is never `0` and every fact that gives it meaning takes
`0 < c`. `descend` and `newtonLift` both read their `M` from here, so they agree by definition. -/
@[expose] def scaler (p : SizedProblem) : Int := 2 ^ ((p.c - 1).fdiv 2).toNat

/-- One reduction step: `(n, c) ↦ (⌊n / 4M²⌋, ⌊c/2⌋)`, carrying the size invariant down to the
child (`size_condition_step`). The divisor `4M²` is the form the algorithm and `key_isqrt_lemma`
divide by; `hc : 0 < p.c` feeds only the child's invariant, so the value fields reduce without it. -/
@[expose] def descend (p : SizedProblem) (hc : 0 < p.c) : SizedProblem :=
  ⟨p.n.fdiv (4 * p.scaler ^ 2), p.c.fdiv 2, size_condition_step rfl hc p.hsc⟩

/-- The Newton combine: lift a value `a` for the descended problem back to one for `p`, as
`Ma + ⌊n / 4Ma⌋`. Paired with `descend` through the shared `scaler`; `isNearSquareRoot_newtonLift`
is the fact that it carries a near square root to a near square root. -/
@[expose] def newtonLift (p : SizedProblem) (a : Int) : Int :=
  p.scaler * a + p.n.fdiv (4 * p.scaler * a)

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
