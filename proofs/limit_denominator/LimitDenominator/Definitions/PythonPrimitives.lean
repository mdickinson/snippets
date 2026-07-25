module

public import LimitDenominator.Definitions.Exceptions

/-!
Lean equivalents of Python's `//`, `%` and `and`, with the same exception-raising and
short-circuiting behaviour as in Python.
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

/--
Python's short-circuiting `and`, for boolean operands. Python always evaluates the left
operand, so only the right one is delayed.

No notation can spell this: Lean's `do` elaborator harvests nested `←` actions from the
*unexpanded* syntax tree, so a macro that wraps its right operand in `do` arrives too late
and silently loses the delay. Write the delayed operand as an explicit `do` block at the
call site instead.
-/
def pyAnd (x : Bool) (y : PyExcept Bool) : PyExcept Bool := do
  if x then y else return false

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
