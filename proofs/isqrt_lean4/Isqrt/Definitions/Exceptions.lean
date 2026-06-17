/-
The exception vocabulary: `PyException` (the Python exceptions `math.isqrt` and its
operations can raise) and the alias `PyExcept α := Except PyException α`.
Core-only: no Mathlib.
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
