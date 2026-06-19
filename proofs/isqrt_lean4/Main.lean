/-
A simple CLI for computing integer square roots.

The executable built from the code below accepts a single nonnegative integer as a
command-line argument, calls `isqrtIterative` on it, and writes the result to stdout. It
returns with exit code 2 and a usage message on stderr if its arguments are malformed.
-/

import Isqrt.Definitions.IsqrtIterative

/-- The message shown on stderr when the command line is malformed. -/
private def usage : String := "usage: isqrt N   (N a nonnegative integer)"

/-- The main entry point. -/
def main (args : List String) : IO UInt32 := do
  try
    let [arg] := args | throw <| .userError usage
    let some n := arg.toNat? | throw <| .userError usage
    let a ← IO.ofExcept (isqrtIterative (n : Int))
    IO.println a
    return (0 : UInt32)
  catch
    | .userError msg =>
      IO.eprintln msg
      return (2 : UInt32)
    | other => throw other
