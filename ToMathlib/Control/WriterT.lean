/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ToMathlib.Control.LawfulFailure
import Mathlib.Control.Monad.Writer

/-!
# Laws for well behaved monadic `failure` operation
-/

universe u v w

namespace WriterT

variable {m : Type u → Type v} [Monad m] {ω : Type u} [Monoid ω]

lemma liftM_def {α : Type u} (x : m α) :
    (liftM x : WriterT ω m α) = WriterT.mk ((·, 1) <$> x) := rfl

lemma monadLift_def {α : Type u} (x : m α) :
    (MonadLift.monadLift x : WriterT ω m α) = WriterT.mk ((·, 1) <$> x) := rfl

lemma bind_def {α β : Type u} (x : WriterT ω m α) (f : α → WriterT ω m β) :
    x >>= f = WriterT.mk (x.run >>= fun (a, w₁) ↦
      (fun (b, w₂) ↦ (b, w₁ * w₂)) <$> (f a)) := rfl

/-- The naturally induced `Failure` on `WriterT` is lawful. -/
instance [Monad m] [LawfulMonad m] [Failure m] [LawfulFailure m] :
    LawfulFailure (WriterT ω m) where
  fail_bind' {α β} f := by
    show WriterT.mk _ = WriterT.mk _
    simp [monadLift_def, map_eq_bind_pure_comp, WriterT.mk, bind_assoc,
      failureOfLift_eq_lift_fail, liftM_def]

instance [LawfulMonad m] : LawfulMonadLift m (WriterT ω m) where
  monadLift_pure x := map_pure (·, 1) x
  monadLift_bind {α β} x y := by
    show WriterT.mk _ = WriterT.mk _
    simp [monadLift_def, map_eq_bind_pure_comp, WriterT.mk, bind_assoc]

end WriterT
