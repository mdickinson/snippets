/-
Library root for the **proofs** component — the correctness theorems and every
supporting lemma. A reader who trusts Lean's checker need not read any of this
beyond the *statements* of the two top-level theorems (`isqrt_eq_ok_iff` in
`Isqrt.Proofs.Correctness`, `isqrtIterative_eq_ok_iff` in
`Isqrt.Proofs.IterativeCorrectness`). This component depends on
`Isqrt.Definitions.*`, never on `Isqrt.Tests.*`.
-/

import Isqrt.Proofs.FDivLemmas
import Isqrt.Proofs.BitLengthLemmas
import Isqrt.Proofs.PythonOpsLemmas
import Isqrt.Proofs.SizeConditions
import Isqrt.Proofs.KeyLemma
import Isqrt.Proofs.Correctness
import Isqrt.Proofs.IterativeCorrectness
