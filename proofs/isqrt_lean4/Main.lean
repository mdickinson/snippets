/-
A simple CLI for computing integer square roots.

The executable built from the code below accepts a single nonnegative integer as a
command-line argument, calls `isqrtIterative` on it, and writes the result to stdout.
It returns with exit code 2 and a usage message on stderr if its arguments are malformed.
-/

module

import Isqrt.Definitions.IsqrtIterative
import Isqrt.Proofs.IterativeCorrectness

/-- The message shown on stderr when the command line is malformed. -/
private def usage : String := "usage: isqrt N   (N a nonnegative integer)"

/--
Wrapper around `isqrtIterative` that accepts a `Nat` and returns a plain `Int`
rather than a `PyExcept Int`, saving us from having to deal with exceptions
in the `main` function.

Defining this function requires that we make use of the proof of correctness
`isCorrectIsqrt_isqrtIterative` for `isqrtIterative`, in order to establish that
`isqrtIterative` doesn't raise on nonnegative inputs.
-/
private def isqrtIterativeNat (n : Nat) : Int :=
  (isqrtIterative n).toOption.get <| by
    have ⟨a, ha, _⟩ := isCorrectIsqrt_isqrtIterative.1 n (Int.natCast_nonneg n)
    have ha' : isqrtIterative n = .ok a := ha
    rw [ha']; rfl

/-- The main entry point. -/
public def main (args : List String) : IO UInt32 := do
  let [arg] := args | IO.eprintln usage; return 2
  let some n := arg.toNat? | IO.eprintln usage; return 2
  IO.println (isqrtIterativeNat n)
  return 0
