/-
Library root for the **proofs** component — the correctness theorems and every
supporting lemma. A reader who trusts Lean's checker need only confirm that the two
top-level theorems (`isCorrectIsqrt_isqrtRecursive` in
`Isqrt.Proofs.RecursiveCorrectness`, `isCorrectIsqrt_isqrtIterative` in
`Isqrt.Proofs.IterativeCorrectness`) assert `isCorrectIsqrt` of the two `isqrt`
translations; the contract itself lives in `Isqrt.Definitions.Specification`. This component
depends on `Isqrt.Definitions.*`, never on `Isqrt.Tests.*`.
-/

module

public import Isqrt.Proofs.FDivLemmas
public import Isqrt.Proofs.PythonPrimitivesLemmas
public import Isqrt.Proofs.SizeConditions
public import Isqrt.Proofs.KeyLemma
public import Isqrt.Proofs.RecursiveCorrectness
public import Isqrt.Proofs.IterativeCorrectness
