/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ToMathlib.Control.FreeMonad

/-!
# Laws for well behaved monadic `failure` operation
-/

universe u v w

-- Stripped down version of `Alternative` to avoid diamonds.
class Failure (m : Type u → Type v) where
  fail {α : Type u} : m α

/-- Typeclass for monads whose `fail` operation ends the computation early,
in the sense that `fail >>= g = fail` and `g` isn't executed. -/
class LawfulFailure (m : Type u → Type v) [h' : Failure m] [h : Monad m] where
  fail_bind' {α β : Type u} (g : α → m β) : Failure.fail >>= g = Failure.fail

section fail

variable {m : Type u → Type v} [h' : Failure m] [h : Monad m]
   [hm : LawfulFailure m] {α β : Type u}

@[simp] lemma fail_bind (g : α → m β) : (Failure.fail : m α) >>= g = Failure.fail :=
  LawfulFailure.fail_bind' g

@[simp] lemma map_fail [LawfulMonad m] (g : α → β) :
    g <$> (Failure.fail : m α) = Failure.fail :=
  by simp [map_eq_bind_pure_comp]

@[simp] lemma fail_seq [LawfulMonad m] (ob : m α) :
    (Failure.fail : m (α → β)) <*> ob = Failure.fail :=
  by simp [seq_eq_bind]

end fail

section Alternative

instance {m : Type u → Type v} [h : Alternative m] : Failure m where
  fail := h.failure

@[simp]
lemma fail_eq_failure (m : Type u → Type v) [Alternative m] (α : Type u) :
    (Failure.fail : m α) = failure := rfl

lemma failure_eq_fail (m : Type u → Type v) [Alternative m] (α : Type u) :
    (failure : m α) = Failure.fail := rfl

variable {m : Type u → Type v} [h' : Alternative m] [h : Monad m]
   [hm : LawfulFailure m] {α β : Type u}

@[simp] lemma failure_bind (g : α → m β) :
    (failure : m α) >>= g = failure :=
  by simp [← fail_eq_failure]

@[simp] lemma map_failure (g : α → β) [LawfulMonad m] :
    h.toApplicative.map g (failure : m α) = failure :=
  by simp [← fail_eq_failure]

@[simp] lemma failure_seq (ob : m α) [LawfulMonad m] :
    h.toApplicative.toSeq.seq (failure : m (α → β)) (λ _ ↦ ob) = failure :=
  by simp [← fail_eq_failure]

end Alternative

/-- Automatically lift failure from inner to outer monad. -/
instance (priority := low) failureOfLift {m : Type u → Type v} [Failure m]
    {n : Type u → Type w} [MonadLift m n] : Failure n where
  fail {α} := liftM (Failure.fail : m α)

lemma failureOfLift_eq_lift_fail {m : Type u → Type v} {n : Type u → Type w} [MonadLift m n]
    [Failure m] {α : Type u} : (Failure.fail : n α) = liftM (Failure.fail : m α) := rfl

section monadLift

variable {m : Type u → Type v} {n : Type u → Type w}
  [Monad m] [Monad n] [Failure m] [Failure n]

/-- Type-class for `LawfulMonadLift`s that also preserve the failure operation. -/
class LawfulFailureLift (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n] [Failure m]
    [Failure n] [MonadLiftT m n] extends LawfulMonadLiftT m n where
  monadLift_fail : {α : Type u} → monadLift (Failure.fail : m α) = (Failure.fail : n α)

@[simp]
lemma liftM_fail [MonadLiftT m n] [LawfulFailureLift m n] {α : Type u} :
    liftM (Failure.fail : m α) = (Failure.fail : n α) :=
  LawfulFailureLift.monadLift_fail

end monadLift
