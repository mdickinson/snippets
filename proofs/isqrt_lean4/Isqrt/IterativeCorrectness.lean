/-
Correctness of the iterative integer square root `isqrtIterative`.

NOTE (for-loop port, definitions only): the loop is now Lean's `for … in … do`
over `(List.range L).reverse` in the `Id` monad, rather than the `pyWhile`
combinator, so the previous proof — which threaded `s, d` in the loop state and
used `pyWhile_invariant` — no longer applies and is left as `sorry` on this branch.

The intended proof reuses the recursive proof's algebra unchanged (one iteration
= one `key_isqrt_lemma` step). It first rewrites the `do`/`forIn'` loop to a
`List.foldl` over the reversed range with the `Init.Data.List.Monadic` bridge
lemmas (e.g. `idRun_forIn'_yield_eq_foldl`), then runs a position-indexed fold
invariant carrying the loop property

    motive s a := isNearSqrt a ⌊n / 4^(c - c>>s)⌋

The `for`-with-proof form (`for h : s in …`) keeps the membership proof
`h : s ∈ (List.range L).reverse`, i.e. `s < L`, available to the body throughout.

The `Nat.foldRev` branch (`isqrt-lean4-foldrev`) carries the fully proved analogue
(`Nat.foldRev_invariant` applied directly, no `forIn → foldl` reduction) and is the
template to follow here.

Gotcha when writing the motive: `py>>` is `infixl:60` and `-` is `infixl:65`, so
`c - c py>> s` parses as `(c - c) py>> s`. Parenthesize: `4^(c - (c py>> s))`.
-/

import Isqrt.Iterative
import Isqrt.KeyLemma

/-! ## Correctness of `isqrtIterative` -/

/-- Main correctness theorem for the iterative form: `isqrtIterative n` is the
floor of `√n`. Same statement as `isqrt_is_sqrt`.

Proof stubbed on this definitions-only branch; see the module note. -/
theorem isqrtIterative_is_sqrt (n : ℤ) (hn : 0 ≤ n) :
    isIntegerSqrt (isqrtIterative n hn) n := by
  sorry
