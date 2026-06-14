/-
The integer-square-root specification predicate. Part of the **definitions**
layer: `isIntegerSquareRoot a n` is the postcondition the top-level correctness
theorems assert, so a reader must read and trust it to know the proofs prove the
right thing. (Its proof-only companion `isNearSquareRoot` lives with the key
algebraic lemma in `Isqrt.Proofs.KeyLemma`.)
-/

/-- `a` is *the* integer square root of `n` if `a² ≤ n < (a + 1)²`, i.e.
`a = ⌊√n⌋` exactly. This is the postcondition the top-level correctness theorems
assert. Stated multiplicatively (`a * a`, not `a ^ 2`) to mirror the Python
postcondition `a * a <= n < (a + 1) * (a + 1)`. -/
def isIntegerSquareRoot (a n : Int) : Prop := a * a ≤ n ∧ n < (a + 1) * (a + 1)
