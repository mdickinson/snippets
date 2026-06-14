/-
The exception vocabulary: how this development models a computation that may
raise, and how it inspects the outcome. Part of the **definitions** layer — the
trust surface — and the foundation both the Python operations
(`Isqrt.Definitions.PythonOps`) and the specification
(`Isqrt.Definitions.Specification`) build on. Core-only: no Mathlib.

Two pieces:

* `PyException`, the concrete Python exceptions `math.isqrt` and the operations it
  uses can raise, together with the alias `PyExcept α := Except PyException α` for
  the result of a computation that may raise one. Every Python operation that can
  raise returns a `PyExcept`, carrying either its result or the exception Python
  would have raised.

* `succeeds`/`fails` and the proof-carrying `returnValue`/`exceptionRaised` —
  accessors on a `PyExcept α` outcome. `succeeds`/`fails` assert that a
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

/-- `PyExcept α` is the type of the result of a computation that either returns a
value of type `α` or raises a Python exception. -/
abbrev PyExcept := Except PyException

namespace Isqrt

/-- Assertion that a computation returned a value (did not raise). -/
def succeeds {α : Type} (x : PyExcept α) : Prop := match x with
  | .ok _ => True
  | .error _ => False

/-- The value returned by a computation that did not raise. -/
def returnValue {α : Type} (x : PyExcept α) (h : succeeds x) : α :=
  match x with
  | .ok a => a

/-- Assertion that a computation raised (did not return a value). -/
def fails {α : Type} (x : PyExcept α) : Prop := match x with
  | .ok _ => False
  | .error _ => True

/-- The exception raised by a computation that did not return. -/
def exceptionRaised {α : Type} (x : PyExcept α) (h : fails x) : PyException :=
  match x with
  | .error e => e

end Isqrt
