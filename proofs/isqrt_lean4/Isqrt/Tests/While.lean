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
second reads its postcondition straight off the return subtype's `¬ guard`.
-/

import Isqrt.While

/-! ## Plain state: count a counter down to zero, accumulating in the second slot

`σ := ℕ × ℕ` as `(counter, acc)`. The guard is `0 < counter`; each step
decrements `counter` and bumps `acc`; the measure is `counter`. -/

private def countDown (s₀ : ℕ × ℕ) : { s : ℕ × ℕ // ¬ 0 < s.1 } :=
  pyWhile (fun s => 0 < s.1) (fun s _ => (s.1 - 1, s.2 + 1)) s₀
    (fun s => s.1) (fun s h => by dsimp only; omega)

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
`0 < second`. The guard is `0 < first`; each step decrements `first` and
*changes* `second` (here doubling it), so the body must re-derive `0 < second`
for the new value from the incoming `s.property` — the proof-carrying pattern
the isqrt body will use to discharge its py-op preconditions (e.g. proving
`0 < a'` for the updated `a` à la `isqrt_aux_return_pos`). The invariant is
genuinely load-bearing: `0 < second * 2` does not follow from the guard alone. -/

/-- The doubled second component stays positive — a toy stand-in for the
isqrt body's `isqrt_aux_return_pos`. -/
private theorem double_pos {m : ℕ} (hm : 0 < m) : 0 < m * 2 := by omega

private def countDownPos (s₀ : { p : ℕ × ℕ // 0 < p.2 }) :
    { s : { p : ℕ × ℕ // 0 < p.2 } // ¬ 0 < s.val.1 } :=
  pyWhile (fun s => 0 < s.val.1)
    (fun s _ => ⟨(s.val.1 - 1, s.val.2 * 2), double_pos s.property⟩) s₀
    (fun s => s.val.1) (fun s h => by dsimp only; omega)

-- The first component drains to 0; the second stays positive (doubling each step).
#guard (countDownPos ⟨(3, 7), by decide⟩).val.val == (0, 56)

/-- The result's first component is zero — read straight off the return
subtype, no induction needed. -/
example (h : 0 < (7 : ℕ)) : (countDownPos ⟨(3, 7), h⟩).val.val.1 = 0 := by
  have := (countDownPos ⟨(3, 7), h⟩).property
  omega
