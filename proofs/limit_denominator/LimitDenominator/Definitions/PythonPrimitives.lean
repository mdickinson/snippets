module

public import LimitDenominator.Definitions.Exceptions

/-!
Lean equivalents of Python's `//` and `%`, with the same exception-raising behaviour as in
Python.
-/

@[expose] public section

/-- The floor of `a / b`, raising `zeroDivisionError` if `b` is zero. -/
def pyFloordiv (a b : Int) : PyExcept Int := do
  if b = 0 then throw <| .zeroDivisionError "division by zero"
  return Int.fdiv a b

/-- Equivalent of Python's `a % b`, raising `zeroDivisionError` if `b` is zero. -/
def pyMod (a b : Int) : PyExcept Int := do
  if b = 0 then throw <| .zeroDivisionError "division by zero"
  return Int.fmod a b

/-
Infix aliases for the Python operations, with precedence chosen to match that of Python;
`open scoped Python` to use them. We bump the priority of `%` to avoid a clash with the
core `HMod.hMod` notation.
-/
namespace Python
@[inherit_doc] scoped infixl:70 "//" => pyFloordiv
@[inherit_doc] scoped infixl:70 (priority := high) "%" => pyMod
end Python

end
