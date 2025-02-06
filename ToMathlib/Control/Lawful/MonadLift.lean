/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Control.Monad.Basic
import Init.Control.State

/-!
# Lawful version of `MonadLift`

This file defines the `LawfulMonadLift` class, which adds laws to the `MonadLift` class.
-/

-- class MonadLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w) where
--   /-- Lifts a value from monad `m` into monad `n`. -/
--   monadLift : {α : Type u} → m α → n α

universe u v w

-- identity layer . return = return
-- composition layer m >>= layer . f = layer (m >>= f)

class LawfulMonadLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [Monad m] [Monad n] [MonadLift m n] : Prop where

  /-- Lifting preserves `pure` -/
  monadLift_pure : {α : Type u} → {a : α} →
    @MonadLift.monadLift m n _ _ (pure a) = pure a

  /-- Lifting preserves `bind` -/
  monadLift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    MonadLift.monadLift ma >>= (MonadLift.monadLift ∘ f) = MonadLift.monadLift (n := n) (ma >>= f)

-- attribute [simp] LawfulMonadLift.monadLift_pure LawfulMonadLift.monadLift_bind

class LawfulMonadLiftT (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [MonadLiftT m n] : Prop where

  /-- Lifting preserves `pure` -/
  monadLift_pure : {α : Type u} → {a : α} →
    @monadLift m n _ _ (pure a) = pure (f := n) a

  /-- Lifting preserves `bind` -/
  monadLift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    monadLift ma >>= (monadLift ∘ f) = monadLift (n := n) (ma >>= f)

export LawfulMonadLift (monadLift_pure monadLift_bind)

attribute [simp] monadLift_pure monadLift_bind

-- namespace LawfulMonadLift

-- variable {m : semiOutParam (Type u → Type v)} {n : Type u → Type w} [Monad m] [Monad n]
--     [MonadLift m n] [LawfulMonadLift m n]

-- end LawfulMonadLift

namespace LawfulMonadLiftT

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n] [MonadLiftT m n]
    [LawfulMonadLiftT m n]

end LawfulMonadLiftT

instance {m : semiOutParam (Type u → Type v)} {n : Type u → Type w} [Monad m] [Monad n]
    [MonadLift m n] [LawfulMonadLift m n] : LawfulMonadLiftT m n where
  monadLift_pure := LawfulMonadLift.monadLift_pure
  monadLift_bind := LawfulMonadLift.monadLift_bind

namespace StateT

variable {σ : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]

#check StateT.run_lift

-- theorem lift_pure

-- theorem lift_bind

instance : LawfulMonadLift m (StateT σ m) where
  monadLift_pure := by
    intro α a
    simp only [MonadLift.monadLift]
    unfold StateT.lift StateT.instMonad StateT.bind StateT.pure
    simp only [bind_pure_comp, map_pure]
  monadLift_bind := by
    intro α β ma f
    simp only [MonadLift.monadLift]
    unfold StateT.lift StateT.instMonad StateT.bind StateT.pure
    simp only [bind_pure_comp, Function.comp_apply, bind_map_left, map_bind]

end StateT
