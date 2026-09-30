module

/-!
Unfolding a `while` loop: one iteration, or all of them.

Lean's `while` elaborates to `Lean.Loop.forIn`, which is built on a `partial def` and
so has no equation lemmas of its own. What it does have is
`Lean.Loop.forIn_eq_of_monadTail`, which unfolds it by one step in any monad carrying a
`Lean.Order.MonadTail` instance — `Except ε` among them. That single step is these two
lemmas: `forIn_loop_peel` where the body iterates, `forIn_loop_done` where it stops.
Induction on the state the caller chooses turns them into termination.

Both are generic and monad-agnostic; nothing about `limit_denominator` appears here.
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
Stopping a `while` loop, given a state at which the body neither raises nor iterates.
-/
public theorem forIn_loop_done
    {m : Type → Type} {α : Type} [Monad m] [LawfulMonad m] [Lean.Order.MonadTail m]
    (body : Unit → α → m (ForInStep α)) {r r' : α}
    (hbody : body () r = pure (ForInStep.done r')) :
    forIn Lean.Loop.mk r body = pure r' := by
  show Lean.Loop.forIn Lean.Loop.mk r body = _
  rw [Lean.Loop.forIn_eq_of_monadTail, hbody, pure_bind]
