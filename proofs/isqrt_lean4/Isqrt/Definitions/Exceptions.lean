/-
The exception vocabulary: `PyException` (the Python exceptions `math.isqrt` and its
operations can raise), the alias `PyExcept α := Except PyException α`, and two
predicates on a `PyExcept` outcome — `returns x a` (it returned `a`) and `raises x e`
(it raised `e`). Core-only: no Mathlib.
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

/-- `returns x a` asserts that the computation `x` returned the value `a` —
i.e. took its `.ok` branch with payload `a`. -/
def returns {α : Type} (x : PyExcept α) (a : α) : Prop := x = .ok a

/-- `raises x e` asserts that the computation `x` raised the exception `e` —
i.e. took its `.error` branch with payload `e`. -/
def raises {α : Type} (x : PyExcept α) (e : PyException) : Prop := x = .error e
