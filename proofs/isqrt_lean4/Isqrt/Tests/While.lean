/-
Sanity checks and ergonomics shakedown for the `pyWhile` combinator.

Two toy loops exercise the combinator end to end:

  - `countDown` over a plain state `σ := ℕ × ℕ`, isolating `pyWhile` and
    `pyWhile_invariant` from any subtype machinery, and
  - `countDownPos` over a *subtype* state, where the body genuinely consumes
    the bundled well-definedness invariant (`s.property`) to typecheck — the
    pattern the iterative isqrt will rely on.

Each `#guard` runs the compiled combinator on a concrete seed (a failing
`#guard` is a build error). The first `example` drives `pyWhile_invariant`; the
second reads its postcondition straight off the return subtype's `¬ condition`.
-/

import Isqrt.While
import Mathlib.Data.Prod.Lex

/-! ## Plain state: count a counter down to zero, accumulating in the second slot

`σ := ℕ × ℕ` as `(counter, acc)`. The condition is `0 < counter`; each step
decrements `counter` and bumps `acc`; the measure is `counter`. -/

private def countDown (initial : ℕ × ℕ) : { s : ℕ × ℕ // ¬ 0 < s.1 } :=
  pyWhile initial (fun s => 0 < s.1) (fun s _ => (s.1 - 1, s.2 + 1))
    (fun s => s.1) (fun s h => by simp_wf; omega)

-- The counter is drained to 0 and everything it held ends up in `acc`.
#guard (countDown (0, 0)).val == (0, 0)
#guard (countDown (3, 0)).val == (0, 3)
#guard (countDown (5, 2)).val == (0, 7)

/-- `counter + acc` is invariant, so once the loop stops (`counter = 0`) the
accumulator holds the whole initial sum. Proved via `pyWhile_invariant`. -/
example (N : ℕ) : (countDown (N, 0)).val.2 = N := by
  have hinv : (countDown (N, 0)).val.1 + (countDown (N, 0)).val.2 = N := by
    unfold countDown
    exact pyWhile_invariant (P := fun s : ℕ × ℕ => s.1 + s.2 = N) (N, 0)
      (by simp) (fun s h hP => by dsimp only at hP ⊢; omega)
  -- The result subtype carries `¬ 0 < counter`, i.e. `counter = 0`.
  have hstop : ¬ 0 < (countDown (N, 0)).val.1 := (countDown (N, 0)).property
  omega

/-! ## Subtype state: the body consumes the bundled invariant

`σ := { p : ℕ × ℕ // 0 < p.2 }` carries the well-definedness invariant
`0 < second`. The condition is `0 < first`; each step decrements `first` and
*changes* `second` (here doubling it), so the body must re-derive `0 < second`
for the new value from the incoming `s.property` — the proof-carrying pattern
the isqrt body will use to discharge its py-op preconditions (e.g. proving
`0 < a'` for the updated `a` à la `isqrt_aux_return_pos`). The invariant is
genuinely load-bearing: `0 < second * 2` does not follow from the condition. -/

/-- The doubled second component stays positive — a toy stand-in for the
isqrt body's `isqrt_aux_return_pos`. -/
private theorem double_pos {m : ℕ} (hm : 0 < m) : 0 < m * 2 := by omega

private def countDownPos (initial : { p : ℕ × ℕ // 0 < p.2 }) :
    { s : { p : ℕ × ℕ // 0 < p.2 } // ¬ 0 < s.val.1 } :=
  pyWhile initial (fun s => 0 < s.val.1)
    (fun s _ => ⟨(s.val.1 - 1, s.val.2 * 2), double_pos s.property⟩)
    (fun s => s.val.1) (fun s h => by simp_wf; omega)

-- The first component drains to 0; the second stays positive (doubling each step).
#guard (countDownPos ⟨(3, 7), by decide⟩).val.val == (0, 56)

/-- The result's first component is zero — read straight off the return
subtype, no induction needed. -/
example (h : 0 < (7 : ℕ)) : (countDownPos ⟨(3, 7), h⟩).val.val.1 = 0 := by
  have := (countDownPos ⟨(3, 7), h⟩).property
  omega

/-! ## Non-ℕ measure: a lexicographic variant for a two-counter loop

The two toys above use an `ℕ` measure; this one exercises the generalisation to
an arbitrary `[WellFoundedRelation α]` by measuring into `ℕ ×ₗ ℕ`
(`Lex (ℕ × ℕ)`, the lexicographic order on pairs).

`odometer` counts a two-digit "odometer" `(major, minor)` down to `(0, 0)`: each
step decrements `minor`, and when `minor` is already 0 it borrows from `major`,
resetting `minor` to `base`. The natural variant is the *pair* ordered
lexicographically — `major` drops on a borrow (with `minor` jumping back up), and
`minor` drops otherwise — which is exactly `μ := toLex`. (A weighted single-`ℕ`
measure like `4·major + minor` also works here, since `minor` stays `≤ 3`: a
weight strictly above that bound makes each borrow a net decrease. The point is
to drive a measure into a non-`ℕ` `α`.) -/

private def odometer (initial : ℕ × ℕ) : { s : ℕ × ℕ // ¬ (0 < s.1 ∨ 0 < s.2) } :=
  pyWhile initial (fun s => 0 < s.1 ∨ 0 < s.2)
    (fun s _ => if 0 < s.2 then (s.1, s.2 - 1) else (s.1 - 1, 3))  -- 3 = base
    (fun s => toLex s)
    (fun s h => by
      -- The measure lives in `ℕ ×ₗ ℕ`, so the decrease is a lexicographic `<`.
      show toLex _ < toLex _
      rw [Prod.Lex.lt_iff]
      -- Strip the `ofLex (toLex …)` round-trips and β-reduce the body lambda, so
      -- `split` sees the `if` and `omega` sees plain projections.
      simp only [ofLex_toLex]
      -- Borrow branch: `major` drops (needs `0 < major`, from `h` since `minor = 0`).
      -- Decrement branch: `major` equal, `minor` drops.
      split <;> omega)

-- Whatever the seed, the odometer winds down to (0, 0).
#guard (odometer (0, 0)).val == (0, 0)
#guard (odometer (2, 0)).val == (0, 0)
#guard (odometer (1, 2)).val == (0, 0)

/-- Both components end at zero — read straight off the return subtype. -/
example : (odometer (2, 1)).val = (0, 0) := by
  have := (odometer (2, 1)).property
  -- `¬ (0 < major ∨ 0 < minor)` forces both to 0; `Prod.ext` then closes it.
  exact Prod.ext (by omega) (by omega)
