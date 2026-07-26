module

public import LimitDenominator.Definitions.LimitDenominatorStdlib
public import LimitDenominator.Definitions.Specification
public import LimitDenominator.Proofs.BestApproximation
import LimitDenominator.Proofs.PythonTranslation
import LimitDenominator.Proofs.WhileLoop

/-!
Correctness of `limitDenominatorStdlib`.

Like `SimplifiedCorrectness`, this file is the mechanics: it names the two halves of the `do`
block, folds the translation onto them, drives the loop with `forIn_loop_invariant`, and reads
the result off. All of the mathematics has already happened, in `BestApproximation`.

The shipped listing's state is the simplified listing's, permuted: its `(p0, q0, p1, q1, n, d)`
is `(p, q, r, s, a, b)` here, so the proof layer's names are used throughout — `a` and `b` for
what the Python calls `n` and `d`, and `k` for the quotient it calls `a`. That makes
`LoopInvariant` reusable unchanged, at the price of two things:

* **The first iteration is peeled off.** It cannot break, its `q2` being `1`, and it computes
  exactly the simplified listing's initialisation, so `LoopInvariant.initial` describes the
  state it lands on. Before it the invariant is false: `s` there is `q1 = 0`.
* **`0 < b` is derived rather than tested.** The shipped loop condition omits that test, so the
  divisor's positivity comes from `LoopInvariant.b_pos`, and that is where the target's being in
  lowest terms earns its place among the hypotheses.

The fast path is none of this: it discharges against the specification directly.
-/

/-- The mutable state of the loop: `(p, q, r, s, a, b)`, the shipped `(p0, q0, p1, q1, n, d)`. -/
abbrev StdlibLoopState := Int × Int × Int × Int × Int × Int

/--
The loop body, named. This is definitionally what `limitDenominatorStdlib`'s `do` block
desugars to, so `limitDenominatorStdlib_fold` folds the loop onto it by `rfl`. The `break` is
the `ForInStep.done`, carrying the state out unchanged.
-/
def stdlibLoopBody (l : Int) (_u : Unit) (state : StdlibLoopState) :
    PyExcept (ForInStep StdlibLoopState) :=
  let ⟨p, q, r, s, a, b⟩ := state
  do
    let k ← pyFloordiv a b
    let q2 := q + k * s
    if q2 > l then
      pure (ForInStep.done state)
    else
      pure (ForInStep.yield (r, s, p + k * r, q2, b, a - k * b))

/--
The tail of the `do` block, named likewise: the extended candidate and the final choice.

Here `n` is the *target's* denominator, the shipped code's `self._denominator`. The Python's
own `n` is the running numerator, which is this state's `_a`, and is unused past the loop.
-/
def stdlibAfterLoop (n l : Int) (state : StdlibLoopState) : PyExcept (Int × Int) :=
  let ⟨p, q, r, s, _a, b⟩ := state
  do
    let k ← pyFloordiv (l - q) s
    if 2 * b * (q + k * s) ≤ n then pure (r, s) else pure (p + k * r, q + k * s)

/-- `limitDenominatorStdlib` past both guards, as a loop followed by its tail. -/
theorem limitDenominatorStdlib_fold {m n l : Int} (hl : 0 < l) (hn : l < n) :
    limitDenominatorStdlib m n l =
      forIn Lean.Loop.mk (0, 1, 1, 0, m, n) (stdlibLoopBody l) >>= stdlibAfterLoop n l := by
  rw [limitDenominatorStdlib, if_neg (by omega), if_neg (by omega)]
  rfl

/-! ## Peeling the first iteration -/

/--
The first iteration in full. Its break test weighs `q + k*s` — here `1 + (m/n)*0`, or just
`1` — against a positive limit, so it never breaks; and it divides by the target's denominator,
so it cannot raise. The state it lands on is the simplified listing's initial state.
-/
theorem stdlibLoopBody_initial {m n l : Int} (hn : 0 < n) (hl : 0 < l) :
    stdlibLoopBody l () (0, 1, 1, 0, m, n)
      = pure (ForInStep.yield (1, 0, m / n, 1, n, m % n)) := by
  have h : m - m / n * n = m % n := by have := Int.mul_ediv_add_emod m n; grind
  rw [stdlibLoopBody, pyFloordiv_ok_bind hn, if_neg (by omega), h]
  simp

/-! ## Driving the loop -/

/-- The loop invariant, as a predicate on the loop's state. -/
def stdlibLoopInvariant (m n l : Int) (state : StdlibLoopState) : Prop :=
  let ⟨p, q, r, s, a, b⟩ := state
  LoopInvariant m n l a b p q r s

/--
The loop invariant together with the negation of the loop condition. Where the simplified
listing's post has a `b = 0` alternative, from the test that guards its division, this one
carries `0 < b`, which `LoopInvariant.b_pos` supplies instead.
-/
def stdlibLoopPost (m n l : Int) (state : StdlibLoopState) : Prop :=
  let ⟨p, q, r, s, a, b⟩ := state
  LoopInvariant m n l a b p q r s ∧ 0 < b ∧ l < q + a / b * s

/--
Under the invariant the body never raises: it either yields a state that still satisfies the
invariant with a strictly smaller `b`, or breaks with the loop condition false. The division is
safe by `LoopInvariant.b_pos`, which is what the two hypotheses on the target are for.
-/
theorem stdlibLoopBody_step {m n l : Int} (hgcd : Int.gcd m n = 1) (hn : l < n)
    (state : StdlibLoopState) (hinv : stdlibLoopInvariant m n l state) :
    (∃ state', stdlibLoopBody l () state = pure (ForInStep.yield state')
        ∧ stdlibLoopInvariant m n l state'
        ∧ state'.2.2.2.2.2.toNat < state.2.2.2.2.2.toNat)
    ∨ (∃ state', stdlibLoopBody l () state = pure (ForInStep.done state')
        ∧ stdlibLoopPost m n l state') := by
  obtain ⟨p, q, r, s, a, b⟩ := state
  have h : LoopInvariant m n l a b p q r s := hinv
  have hb : 0 < b := h.b_pos hgcd hn
  have hmod : a - a / b * b = a % b := by have := Int.mul_ediv_add_emod a b; grind
  rw [stdlibLoopBody, pyFloordiv_ok_bind hb, hmod]
  -- Beta-reduce the `q2` binding, which `split` cannot see past.
  simp only []
  split
  · exact .inr ⟨_, rfl, h, hb, by omega⟩
  · exact .inl ⟨_, rfl, h.step hb (by omega),
      (Int.toNat_lt_toNat hb).mpr (Int.emod_lt_of_pos a hb)⟩

/--
Correctness of `limitDenominatorStdlib`: for a denominator limit that is not positive it raises
the same `ValueError` as CPython, and for a target in lowest terms with positive denominator —
which is every target a `Fraction` can hold — it returns the best approximation.
-/
public theorem isCorrectLimitDenominator_stdlib :
    isCorrectLimitDenominator (fun m n => 0 < n ∧ Int.gcd m n = 1) limitDenominatorStdlib := by
  refine ⟨?_, ?_⟩
  · -- A nonpositive limit: the first guard raises, short-circuiting the `do` block.
    intro m n l hl
    rw [limitDenominatorStdlib, if_pos (show l < 1 by omega)]
    rfl
  · intro m n l ⟨hn, hgcd⟩ hl
    rcases (by omega : n ≤ l ∨ l < n) with hfast | hslow
    · -- The fast path returns the target itself.
      refine ⟨m, n, ?_, isBestApproximation_self hn hfast hgcd⟩
      rw [limitDenominatorStdlib, if_neg (by omega), if_pos hfast]
      rfl
    -- Otherwise the loop runs, never raises, and returns one of the two candidates.
    rw [limitDenominatorStdlib_fold hl hslow, forIn_loop_peel _ (stdlibLoopBody_initial hn hl)]
    obtain ⟨y, hy_eq, hy_post⟩ := forIn_loop_invariant
      (fun state => state.2.2.2.2.2.toNat) (stdlibLoopBody l) (stdlibLoopInvariant m n l)
      (stdlibLoopPost m n l) (stdlibLoopBody_step hgcd hslow) (1, 0, m / n, 1, n, m % n)
      (LoopInvariant.initial hn hl)
    rw [hy_eq]
    obtain ⟨p, q, r, s, a, b⟩ := y
    obtain ⟨hinv, hb, hexit⟩ :
        LoopInvariant m n l a b p q r s ∧ 0 < b ∧ l < q + a / b * s := hy_post
    rw [stdlibAfterLoop, pyFloordiv_ok_bind hinv.s_pos]
    have hbracket := hinv.bracketing (.inr ⟨hb, hexit⟩) rfl rfl rfl rfl
    split <;> rename_i hchoice
    · exact ⟨r, s, rfl,
        hbracket.isBestApproximation_loop (hbracket.loop_nearer_iff.mp hchoice)⟩
    · exact ⟨_, _, rfl,
        hbracket.isBestApproximation_extended
          (by have := hbracket.loop_nearer_iff; omega)⟩
