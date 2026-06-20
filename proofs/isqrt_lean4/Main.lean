/-
A simple CLI for computing integer square roots.

The executable built from the code below accepts a single nonnegative integer as a
command-line argument, calls `isqrtIterativeNat` on it, and writes the result to stdout.
It returns with exit code 2 and a usage message on stderr if its arguments are malformed.

`isqrtIterativeNat` is total — it never raises — so the CLI has no computation-failure
case to handle. The only error path is a malformed command line.
-/

module

import Isqrt.Proofs.IterativeCorrectness

/-- The message shown on stderr when the command line is malformed. -/
private def usage : String := "usage: isqrt N   (N a nonnegative integer)"

/-- The main entry point. -/
public def main (args : List String) : IO UInt32 := do
  let [arg] := args | IO.eprintln usage; return 2
  let some n := arg.toNat? | IO.eprintln usage; return 2
  IO.println (isqrtIterativeNat n)
  return 0
