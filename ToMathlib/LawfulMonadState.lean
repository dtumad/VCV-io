/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
-- import VCVio
import Mathlib.Control.Monad.Basic

/-!
# Lawful MonadState

This file defines the `LawfulMonadState` class, which adds laws to the `MonadState` class.
-/

#check MonadStateOf

#check MonadState

universe u v

class LawfulMonadStateOf (σ : outParam (Type u)) (m : Type u → Type v) extends
    Monad m, MonadStateOf σ m : Type (max (u+1) v) where
  /-- `modifyGet f` is equivalent to `do let (a, s) := f (← get); put s; pure a` -/
  modifyGet_eq : {α : Type u} → (f : σ → α × σ) →
    modifyGet f = do let (a, s) := f (← get); set s; pure a

export LawfulMonadStateOf (modifyGet_eq)

-- Should this be simp?
attribute [simp] LawfulMonadStateOf.modifyGet_eq

section LawfulMonadStateOf

variable {σ : Type u} {m : Type u → Type v}

@[simp]
theorem modifyGetThe_eq [MonadStateOf σ m] {α : Type u} (f : σ → α × σ) :
    modifyGetThe σ (m := m) f = MonadStateOf.modifyGet f := rfl

variable [LawfulMonadStateOf σ m] [LawfulMonad m]

-- Should this be simp?
@[simp]
theorem modifyThe_eq (f : σ → σ) :
    modifyThe σ (m := m) f = MonadStateOf.get >>= (fun s => set (f s)) := by
  simp only [modifyThe, modifyGet_eq, bind_pure_comp, id_map']


end LawfulMonadStateOf

  -- /-- `modify f` is equivalent to `do set (f (← get))` -/
  -- modify_eq_set_get : (f : σ → σ) → modify f = bind get (fun s => set (f s))
  -- /-- `getModify f` is equivalent to `get <* modify f` -/
  -- getModify_eq_get_seqLeft_modify : (f : σ → σ) → getModify f = seqLeft get (fun _ => modify f)

class LawfulMonadState (σ : outParam (Type u)) (m : Type u → Type v) extends
    Monad m, MonadState σ m : Type (max (u+1) v) where
  /-- `modifyGet f` is equivalent to `do let (a, s) := f (← get); put s; pure a` -/
  modifyGet_eq : {α : Type u} → (f : σ → α × σ) →
    modifyGet f = do let (a, s) := f (← get); set s; pure a

export LawfulMonadState (modifyGet_eq)

attribute [simp] LawfulMonadState.modifyGet_eq

  -- /-- `modify f` is equivalent to `do set (f (← get))` -/
  -- modify_eq_set_get' : (f : σ → σ) → modify f = bind get (fun s => set (f s))
  -- /-- `getModify f` is equivalent to `get <* modify f` -/
  -- getModify_eq_get_seqLeft_modify' : (f : σ → σ) → getModify f = seqLeft get (fun _ => modify f)

variable {σ : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadState σ m] [LawfulMonadState σ m]

-- @[simp] theorem modifyGet_eq_bind_get_set_pure {α : Type u} (f : σ → α × σ) :
--     modifyGet f = get >>= (fun s => let p := f s; bind (set p.2) (fun _ => pure p.1)) :=
--   LawfulMonadState.modifyGet_eq f

-- @[simp] theorem modify_eq_set_get (f : σ → σ) :
--     modify f = get >>= (fun s => set (f s)) :=
--   LawfulMonadState.modify_eq_set_get' f

-- @[simp] theorem getModify_eq_get_seqLeft_modify (f : σ → σ) :
--     getModify f = get <* (fun _ => modify f) :=
--   LawfulMonadState.getModify_eq_get_seqLeft_modify' f

section StateT

instance : LawfulMonadStateOf σ (StateT σ m) := sorry

end StateT
