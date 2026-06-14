/-
Value-extraction lemmas for the `Except`-returning Python operations of
`Isqrt.Definitions.PythonOps`.

On its non-raising branch each operation returns `.ok` of the corresponding
`Int.fdiv` / power-of-two value. These are the bridges the correctness proofs use
to step through the `do`-block once they have discharged the side conditions
(nonzero divisor, nonneg shift). Their right-hand sides mention only `Int.fdiv`
and powers of two, so the proofs can rewrite with them directly.
-/

import Isqrt.Definitions.PythonOps

/-- For a nonzero divisor, `pyFloordiv` takes its `.ok` branch. -/
theorem pyFloordiv_eq_ok {a b : Int} (hb : b ≠ 0) :
    pyFloordiv a b = .ok (Int.fdiv a b) := by
  unfold pyFloordiv; split
  · omega
  · rfl

/-- For a nonneg shift count, `pyLshift` takes its `.ok` branch. -/
theorem pyLshift_eq_ok {n k : Int} (hk : 0 ≤ k) :
    pyLshift n k = .ok (n * 2 ^ k.toNat) := by
  unfold pyLshift; split
  · omega
  · rfl

/-- For a nonneg shift count, `pyRshift` takes its `.ok` branch. -/
theorem pyRshift_eq_ok {n k : Int} (hk : 0 ≤ k) :
    pyRshift n k = .ok (Int.fdiv n (2 ^ k.toNat)) := by
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
