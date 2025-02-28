/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ToMathlib.General
import Mathlib.Control.Monad.AlternativeMonad
import Batteries.Control.Lawful.MonadLift

/-!
# Laws for well behaved monadic `failure` operation
-/

universe u v w

section monadLift

variable {m : Type u → Type v} {n : Type u → Type w}
  [AlternativeMonad m] [AlternativeMonad n]

/-- Type-class for `LawfulMonadLift`s that also preserve the failure operation. -/
class LawfulAlternativeLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [AlternativeMonad m] [AlternativeMonad n] [MonadLift m n] extends LawfulMonadLift m n where
  monadLift_failure {α : Type u} : monadLift (failure : m α) = (failure : n α)
  monadLift_orElse {α : Type u} (x y : m α) :
    monadLift (x <|> y) = (monadLift x <|> monadLift y : n α)

export LawfulAlternativeLift (monadLift_failure monadLift_orElse)
attribute [simp] monadLift_failure monadLift_orElse

variable [MonadLift m n] [LawfulAlternativeLift m n] {α β γ : Type u}

@[simp]
lemma liftM_failure : liftM (failure : m α) = (failure : n α) := monadLift_failure

@[simp]
lemma liftM_orElse (x y : m α) : liftM (x <|> y) = (liftM x <|> liftM y : n α) :=
  monadLift_orElse x y

-- instance {σ : Type u} : LawfulAlternativeLift m (StateT σ m) where

end monadLift
