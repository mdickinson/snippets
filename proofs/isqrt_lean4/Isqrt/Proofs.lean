/-
Library root for the **proofs** component — the correctness theorems and every
supporting lemma. A reader who trusts Lean's checker need only confirm that the two
top-level theorems (`isCorrectIsqrt_isqrtRecursive` in
`Isqrt.Proofs.RecursiveCorrectness`, `isCorrectIsqrt_isqrtIterative` in
`Isqrt.Proofs.IterativeCorrectness`) assert `isCorrectIsqrt` of the two `isqrt`
translations; the contract itself lives in `Isqrt.Definitions.Specification`. This component
depends on `Isqrt.Definitions.*`, never on `Isqrt.Tests.*`.
-/

import Isqrt.Proofs.FDivLemmas
import Isqrt.Proofs.BitLengthLemmas
import Isqrt.Proofs.PythonOpsLemmas
import Isqrt.Proofs.SizeConditions
import Isqrt.Proofs.KeyLemma
import Isqrt.Proofs.RecursiveCorrectness
import Isqrt.Proofs.IterativeCorrectness
