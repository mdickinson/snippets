/-
The exception vocabulary: `PyException` (the Python exceptions `math.isqrt` and its
operations can raise), the alias `PyExcept α := Except PyException α`, and four
accessors on a `PyExcept` outcome — `succeeds`/`fails` (did it return / raise) and
the proof-carrying `returnValue`/`exceptionRaised` (the returned value / raised
exception, given a proof the computation took that branch). Core-only: no Mathlib.

The accessors sit in the project's `Isqrt` namespace to avoid a clash with
Mathlib's own `succeeds`.
-/

/-- The Python exceptions that `math.isqrt` and the operations it uses can raise. -/
inductive PyException where
  | zeroDivisionError
  | valueError (msg : String)
  deriving Repr

/--
`PyExcept α` represents the result of a computation that either returns a value of type
`α` or raises a Python exception.
-/
abbrev PyExcept := Except PyException

namespace Isqrt

/-- Assertion that a computation returned a value (did not raise). -/
def succeeds {α : Type} : (x : PyExcept α) → Prop
  | .ok _ => True
  | .error _ => False

/-- Assertion that a computation raised (did not return a value). -/
def fails {α : Type} : (x : PyExcept α) → Prop
  | .ok _ => False
  | .error _ => True

/-- The value returned by a computation that did not raise. -/
def returnValue {α : Type} : (x : PyExcept α) → (h : succeeds x) → α
  | .ok a, _ => a

/-- The exception raised by a computation that did not return. -/
def exceptionRaised {α : Type} : (x : PyExcept α) → (h : fails x) → PyException
  | .error e, _ => e

end Isqrt
