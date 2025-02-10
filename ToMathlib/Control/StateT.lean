/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ToMathlib.Control.FreeMonad
import ToMathlib.Control.LawfulFailure
import ToMathlib.General

/-!
# Lemmas about `StateT`
-/

universe u v w

namespace StateT

variable {m : Type u → Type v} {m' : Type u → Type w}
  {σ α β : Type u}

instance [MonadLift m m'] : MonadLift (StateT σ m) (StateT σ m') where
  monadLift x := StateT.mk fun s => liftM ((x.run) s)

@[simp]
lemma liftM_of_liftM_eq [MonadLift m m'] (x : StateT σ m α) :
    (liftM x : StateT σ m' α) = StateT.mk fun s => liftM (x.run s) := rfl

lemma liftM_def [Monad m] (x : m α) : (x : StateT σ m α) = StateT.lift x := rfl

-- TODO: should this be simp?
lemma monad_pure_def [Monad m] (x : α) :
    (pure x : StateT σ m α) = StateT.pure x := rfl

@[simp]
lemma monad_failure_eq [Monad m] [Alternative m] :
    (failure : StateT σ m α) = StateT.failure := rfl

@[simp]
lemma fail_eq [Monad m] [Alternative m] :
    (Failure.fail : StateT σ m α) = StateT.failure := rfl

@[simp]
lemma run_failure [Monad m] [Alternative m] (s : σ) :
    (StateT.failure : StateT σ m α).run s = failure := rfl

@[simp]
lemma mk_eq_pure [Monad m] (x : α) :
  StateT.mk (λ s ↦ pure (x, s)) = (pure x : StateT σ m α) := rfl

@[simp]
lemma lift_failure [Alternative m] [Monad m] [LawfulFailure m] :
    (StateT.lift (failure : m α) : StateT σ m α) = StateT.failure :=
  StateT.ext fun x => by simp

instance {m : Type u → Type v} {σ : Type u} [Failure m] [Monad m] [LawfulFailure m] :
    LawfulFailure (StateT σ m) where
  fail_bind' x := StateT.ext fun x => by
    simp [run]
    sorry

end StateT
