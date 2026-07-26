module

/-!
Unfolding a `while` loop: one iteration, or all of them.

Lean's `while` elaborates to `Lean.Loop.forIn`, which is built on a `partial def` and so has
no equation lemmas of its own. What it does have is `Lean.Loop.forIn_eq_of_monadTail`, which
unfolds it by one step in any monad carrying a `Lean.Order.MonadTail` instance — `Except ε`
among them. That single step is `forIn_loop_peel`; strong induction on a measure turns it into
termination, which is `forIn_loop_invariant`.

Both lemmas are generic and monad-agnostic; nothing about `limit_denominator` appears here.
-/

/--
Peeling one iteration off the front of a `while` loop, given a state at which the body neither
raises nor exits.
-/
public theorem forIn_loop_peel
    {m : Type → Type} {α : Type} [Monad m] [LawfulMonad m] [Lean.Order.MonadTail m]
    (body : Unit → α → m (ForInStep α)) {r r' : α}
    (hbody : body () r = pure (ForInStep.yield r')) :
    forIn Lean.Loop.mk r body = forIn Lean.Loop.mk r' body := by
  show Lean.Loop.forIn Lean.Loop.mk r body = _
  rw [Lean.Loop.forIn_eq_of_monadTail, hbody, pure_bind]
  rfl

/--
Threading a measure and an invariant through a `while` loop.

Each iteration either yields a state that still satisfies `invariant` with a strictly smaller
`measure`, or finishes with a state satisfying `post`. The conclusion is that the loop returns
without raising, and that its result satisfies `post`.
-/
public theorem forIn_loop_invariant
    {m : Type → Type} {α : Type} [Monad m] [LawfulMonad m] [Lean.Order.MonadTail m]
    (measure : α → Nat)
    (body : Unit → α → m (ForInStep α))
    (invariant post : α → Prop)
    (hstep : ∀ r, invariant r →
      (∃ r', body () r = pure (ForInStep.yield r') ∧ invariant r' ∧ measure r' < measure r) ∨
      (∃ r', body () r = pure (ForInStep.done r') ∧ post r'))
    (r : α) (hr : invariant r) :
    ∃ y, (∀ {β : Type} (g : α → m β), forIn Lean.Loop.mk r body >>= g = g y) ∧ post y := by
  suffices h : ∃ y, forIn Lean.Loop.mk r body = pure y ∧ post y by
    obtain ⟨y, hy, hpost⟩ := h
    exact ⟨y, fun g => by rw [hy, pure_bind], hpost⟩
  generalize hk : measure r = k
  induction k using Nat.strongRecOn generalizing r with
  | _ k ind =>
    show ∃ y, Lean.Loop.forIn Lean.Loop.mk r body = pure y ∧ post y
    rw [Lean.Loop.forIn_eq_of_monadTail]
    rcases hstep r hr with ⟨r', hbody, hinv, hlt⟩ | ⟨r', hbody, hpost⟩
    · rw [hbody, pure_bind]
      exact ind (measure r') (by omega) r' hinv rfl
    · rw [hbody, pure_bind]
      exact ⟨r', rfl, hpost⟩
