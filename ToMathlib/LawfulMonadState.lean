/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
-- import VCVio
import Mathlib.Control.Monad.Basic
import Init.Control.State

/-!
# Lawful MonadState

This file defines the `LawfulMonadState` class, which adds laws to the `MonadState` class.

TODO: what about `LawfulMonad{Control/Reader/Writer/Option}`?
-/

universe u v

class LawfulMonadStateOf (σ : outParam (Type u)) (m : Type u → Type v) extends
    Monad m, MonadStateOf σ m : Type (max (u+1) v) where
  /-- `modifyGet f` is equivalent to `do let (a, s) := f (← get); put s; pure a` -/
  modifyGet_eq : {α : Type u} → (f : σ → α × σ) →
    modifyGet f = do let (a, s) := f (← get); set s; pure a

-- Should this be simp?
attribute [simp] LawfulMonadStateOf.modifyGet_eq

namespace LawfulMonadStateOf

variable {σ : Type u} {m : Type u → Type v}

@[simp]
theorem getThe_eq [MonadStateOf σ m] : getThe σ (m := m) = MonadStateOf.get := rfl

@[simp]
theorem modifyGetThe_eq [MonadStateOf σ m] {α : Type u} (f : σ → α × σ) :
    modifyGetThe σ (m := m) f = MonadStateOf.modifyGet f := rfl

variable [LawfulMonadStateOf σ m] [LawfulMonad m]

-- Should this be simp?
@[simp]
theorem modifyThe_eq (f : σ → σ) :
    modifyThe σ (m := m) f = (do set (f (← MonadStateOf.get))) := by
  simp only [modifyThe, modifyGet_eq, bind_pure_comp, id_map']

end LawfulMonadStateOf

class LawfulMonadState (σ : outParam (Type u)) (m : Type u → Type v) extends
    Monad m, MonadState σ m : Type (max (u+1) v) where
  /-- `modifyGet f` is equivalent to `do let (a, s) := f (← get); put s; pure a` -/
  modifyGet_eq : {α : Type u} → (f : σ → α × σ) →
    modifyGet f = do let (a, s) := f (← get); set s; pure a
  -- Is the below the right property?
  -- get_get : (do let _ ← get; get) = get

export LawfulMonadState (modifyGet_eq)

attribute [simp] LawfulMonadState.modifyGet_eq

namespace LawfulMonadState

variable {σ : Type u} {m : Type u → Type v} [LawfulMonadState σ m] [LawfulMonad m]

-- @[simp] theorem modifyGet_eq_bind_get_set_pure {α : Type u} (f : σ → α × σ) :
--     modifyGet f = get >>= (fun s => let p := f s; bind (set p.2) (fun _ => pure p.1)) :=
--   LawfulMonadState.modifyGet_eq f

@[simp]
theorem modify_eq (f : σ → σ) :
    modify (m := m) f = (do MonadState.set (f (← get))) := by
  simp only [modify, modifyGet_eq, bind_pure_comp, id_map']

-- Do we need extra property of `get` here? That `get` twice is the same as `get` once?
@[simp] theorem getModify_eq (f : σ → σ) :
    getModify (m := m) f = get <* modify f := by
  simp [getModify, seqLeft_eq_bind]
  sorry

end LawfulMonadState

section StateT

variable {σ : Type u} {m : Type u → Type v} [Monad m]

instance : LawfulMonadStateOf σ (StateT σ m) where
  modifyGet_eq f := by
    simp [MonadStateOf.modifyGet, MonadStateOf.get, MonadStateOf.set, pure]
    unfold StateT.modifyGet StateT.get StateT.set StateT.pure StateT.instMonad StateT.bind
    funext s
    simp
    sorry

end StateT
