/-
This module introduces a `PyException` type representing the Python exceptions that
we need to model (just `ValueError` and `ZeroDivisionError`), and the corresponding
`PyExcept` monad.
-/

/-- The Python exceptions that `math.isqrt` and the operations it uses can raise. -/
inductive PyException where
  | zeroDivisionError (msg : String)
  | valueError (msg : String)
  deriving Repr

/--
`PyExcept α` represents the result of a computation that either returns a value of type
`α` or raises a Python exception.
-/
abbrev PyExcept := Except PyException
