/-
The exception vocabulary: how this development models a computation that may
raise, and how it inspects the outcome. Part of the **definitions** layer — the
trust surface — and the foundation both the Python operations
(`Isqrt.Definitions.PythonOps`) and the specification
(`Isqrt.Definitions.Specification`) build on. Core-only: no Mathlib.

Two pieces:

* `PyException` — the concrete Python exceptions `math.isqrt` and the operations
  it uses can raise. Every Python operation that can raise is modelled as an
  `Except PyException`, carrying either its result or the exception Python would
  have raised.

* `succeeds`/`fails` and the proof-carrying `returnValue`/`exceptionRaised` —
  generic accessors on an `Except ε α` outcome. `succeeds`/`fails` assert that a
  computation returned / raised; `returnValue`/`exceptionRaised` then extract the
  returned value / raised exception, each total only given a proof that the
  computation took that branch. They live in the project's own `Isqrt` namespace
  (not grafted onto `Except`) so the specification can write
  `Isqrt.succeeds (isqrt n)` without colliding with Mathlib's own `succeeds`.
-/

/-- The Python exceptions that `math.isqrt` and the operations it uses can raise.
`deriving Repr` lets `#eval` print the exception's contents in tests (the analogue
of a Python `__repr__`). -/
inductive PyException where
  | zeroDivisionError
  | valueError (msg : String)
  deriving Repr

namespace Isqrt

/-- Assertion that a computation didn't raise. -/
def succeeds {ε α : Type _} (x : Except ε α) : Prop := match x with
  | .ok _ => True
  | .error _ => False

/-- The return value from a computation that didn't raise. -/
def returnValue {ε α : Type _} (x : Except ε α) (p : succeeds x) : α :=
  match x with
  | .ok a => a

/-- Assertion that a computation failed. -/
def fails {ε α : Type _} (x : Except ε α) : Prop := match x with
  | .ok _ => False
  | .error _ => True

/-- The exception raised by a failed computation. -/
def exceptionRaised {ε α : Type _} (x : Except ε α) (p : fails x) : ε :=
  match x with
  | .error e => e

end Isqrt
