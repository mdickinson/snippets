module

import LimitDenominator.Definitions.LimitDenominatorSimplified
import LimitDenominator.Proofs.SimplifiedCorrectness

/-!
A simple CLI for finding the closest fraction with a bounded denominator.

The CLI accepts three integer arguments `m n l`, applies `limitDenominatorSimplified` to them,
and writes the resulting fraction to stdout as `r/s`. The `ValueError`s that the algorithm
raises on a bad limit or a bad target denominator are reported to the user; the correctness
proof is what lets the `ZeroDivisionError` case be dismissed as impossible.

The proved definition is called here, never transcribed. A `while` translation is opaque to
the kernel, so there is no `rfl` on a concrete input to hold an independent copy against, and
nothing in the build would catch one that had drifted.
-/

/-- The message shown on stderr when the command line is malformed. -/
private def usage : String := "usage: limit_denominator M N L   (M, N, L integers)"

/--
The closest fraction to `m / n` with denominator at most `l`, or the message of the
`ValueError` explaining why there is none.

The algorithm can in principle also raise `ZeroDivisionError`, which would leave this
function with nothing to return. `limitDenominatorSimplified_total` says that cannot happen
for any `m`, `n` and `l`, so that branch is discharged rather than handled.
-/
private def limitDenominatorOrMessage (m n l : Int) : Except String (Int × Int) :=
  match h : limitDenominatorSimplified m n l with
  | .ok (r, s) => .ok (r, s)
  | .error (.valueError msg) => .error msg
  | .error (.zeroDivisionError _) =>
    absurd (limitDenominatorSimplified_total m n l) (by simp [raises, returns, h])

/-- The main entry point. -/
public def main (args : List String) : IO UInt32 := do
  let [marg, narg, larg] := args | IO.eprintln usage; return 2
  let some m := marg.toInt? | IO.eprintln usage; return 2
  let some n := narg.toInt? | IO.eprintln usage; return 2
  let some l := larg.toInt? | IO.eprintln usage; return 2
  match limitDenominatorOrMessage m n l with
  | .ok (r, s) => IO.println s!"{r}/{s}"; return 0
  | .error msg => IO.eprintln s!"ValueError: {msg}"; return 1
