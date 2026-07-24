module

import Isqrt.Definitions.IsqrtIterative
import Isqrt.Proofs.IterativeCorrectness

/-!
A simple CLI for computing integer square roots.

The CLI accepts a single nonnegative integer argument, applies `isqrtIterative` to it,
and writes the resulting integer square root to stdout.
-/

/-- The message shown on stderr when the command line is malformed. -/
private def usage : String := "usage: isqrt N   (N a nonnegative integer)"

/-- Wrapper around `isqrtIterative` that accepts a `Nat` and returns a plain `Int`. -/
private def isqrtIterativeNat (n : Nat) : Int :=
  (isqrtIterative n).toOption.get <| by
    obtain ⟨a, ha, _⟩ := isCorrectIsqrt_isqrtIterative.2 (Int.natCast_nonneg n)
    rw [show isqrtIterative n = .ok a from ha]; rfl

/-- The main entry point. -/
public def main (args : List String) : IO UInt32 := do
  let [arg] := args | IO.eprintln usage; return 2
  let some n := arg.toNat? | IO.eprintln usage; return 2
  IO.println (isqrtIterativeNat n)
  return 0
