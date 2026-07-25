module

public import LimitDenominator.Definitions.PythonPrimitives

/-!
Bridges from the Python primitives to the pure `Int` forms the correctness proofs reason with.

Every divisor in the algorithm is positive, and `Int.fdiv_eq_ediv_of_nonneg` /
`Int.fmod_eq_emod_of_nonneg` condition on the divisor, so the proof layer sees only Euclidean
`/` and `%` after these two rewrites — `Int.fdiv` and `Int.fmod` appear nowhere else.
-/

/-
The Python `//` and `%` notation is deliberately left closed here: this file is where the two
spellings meet, so both operands of each bridge are written out in full.
-/

/-- For a positive divisor, Python's `a // b` returns `.ok (a / b)`. -/
public theorem pyFloordiv_ok_bind {α : Type} {a b : Int} (hb : 0 < b) (f : Int → PyExcept α) :
    (pyFloordiv a b >>= f) = f (a / b) := by
  rw [pyFloordiv, if_neg (by omega), Int.fdiv_eq_ediv_of_nonneg _ (by omega)]; rfl

/-- For a positive divisor, Python's `a % b` returns `.ok (a % b)`. -/
public theorem pyMod_ok_bind {α : Type} {a b : Int} (hb : 0 < b) (f : Int → PyExcept α) :
    (pyMod a b >>= f) = f (a % b) := by
  rw [pyMod, if_neg (by omega), Int.fmod_eq_emod_of_nonneg _ (by omega)]; rfl

/-- With a false left operand, `pyAnd` short-circuits: the right operand is never run. -/
public theorem pyAnd_false (y : PyExcept Bool) : pyAnd false y = pure false := rfl

/-- With a true left operand, `pyAnd` is its right operand. -/
public theorem pyAnd_true (y : PyExcept Bool) : pyAnd true y = y := rfl
