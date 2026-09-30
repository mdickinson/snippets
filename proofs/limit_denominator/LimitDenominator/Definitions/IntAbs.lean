module

/-! Absolute value on `Int`. -/

/-- Absolute value of an integer. -/
@[expose] public def Int.abs (a : Int) : Int := if 0 ≤ a then a else -a
