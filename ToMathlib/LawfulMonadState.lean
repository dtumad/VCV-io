/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
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

  /-- `modifyGet f` is equivalent to `do let (a, s) := f (← get); set s; pure a` -/
  modifyGet_eq : {α : Type u} → (f : σ → α × σ) →
    modifyGet f = do let (a, s) := f (← get); set s; pure a

  /-- `get` twice doesn't change the state -/
  get_get : {α : Type u} → {a : σ → σ → m α} →
    (do let s₁ ← get; let s₂ ← get; a s₁ s₂) = (do let s ← get; a s s)

  /-- `set` twice has the same effect as the second `set` -/
  set_set : {s₁ s₂ : σ} → (do set s₁; set s₂) = set s₂

  /-- Getting the state after setting it returns the `set` value -/
  get_set : {s : σ} → (do set s; get) = (do set s; pure s)

  /-- Setting the state to the value just gotten is redundant -/
  set_get : (do let s ← get; set s) = pure ⟨⟩

-- Should this be simp?
attribute [simp] LawfulMonadStateOf.modifyGet_eq
  LawfulMonadStateOf.get_get LawfulMonadStateOf.set_set
  LawfulMonadStateOf.get_set LawfulMonadStateOf.set_get

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

  /-- `modifyGet f` is equivalent to `do let (a, s) := f (← get); set s; pure a` -/
  modifyGet_eq : {α : Type u} → (f : σ → α × σ) →
    modifyGet f = do let (a, s) := f (← get); set s; pure a

  /-- `get` twice doesn't change the state -/
  get_get : {α : Type u} → {a : σ → σ → m α} →
    (do let s₁ ← get; let s₂ ← get; a s₁ s₂) = (do let s ← get; a s s)

  /-- `set` twice has the same effect as the second `set` -/
  set_set : {s₁ s₂ : σ} → (do set s₁; set s₂) = set s₂

  /-- Getting the state after setting it returns the `set` value -/
  get_set : {s : σ} → (do set s; get) = (do set s; pure s)

  /-- Setting the state to the value just gotten is redundant -/
  set_get : (do let s ← get; set s) = pure ⟨⟩

attribute [simp] LawfulMonadState.modifyGet_eq LawfulMonadState.get_get
  LawfulMonadState.set_set LawfulMonadState.get_set LawfulMonadState.set_get

namespace LawfulMonadState

variable {σ : Type u} {m : Type u → Type v} [LawfulMonadState σ m] [LawfulMonad m]

@[simp]
theorem modify_eq (f : σ → σ) :
    modify (m := m) f = (do MonadState.set (f (← get))) := by
  simp only [modify, modifyGet_eq, bind_pure_comp, id_map']

-- Do we need extra property of `get` here? That `get` twice is the same as `get` once?
@[simp]
theorem getModify_eq (f : σ → σ) :
    getModify (m := m) f = get <* modify f := by
  simp [getModify, seqLeft_eq_bind]

end LawfulMonadState

instance {σ : Type u} {m : Type u → Type v} [LawfulMonadStateOf σ m] :
    LawfulMonadState σ m where
  modifyGet_eq f := LawfulMonadStateOf.modifyGet_eq f
  get_get := LawfulMonadStateOf.get_get
  set_set := LawfulMonadStateOf.set_set
  get_set := LawfulMonadStateOf.get_set
  set_get := LawfulMonadStateOf.set_get

namespace StateT

variable {σ : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]

@[simp]
theorem modifyGet_eq_monadState {α : Type u} (f : σ → α × σ) :
    StateT.modifyGet (m := m) f = (do let (a, s) := f (← StateT.get); StateT.set s; pure a) := by
  unfold StateT.modifyGet StateT.get StateT.set StateT.instMonad StateT.bind StateT.pure
  simp only [bind_pure_comp, map_pure]

@[simp]
theorem get_get {α : Type u} {a : σ → σ → StateT σ m α} :
    (do let s₁ ← StateT.get; let s₂ ← StateT.get; a s₁ s₂) = (do let s ← StateT.get; a s s) := by
  unfold StateT.get StateT.instMonad StateT.bind
  simp only [pure_bind]

@[simp]
theorem set_set {s₁ s₂ : σ} : (do StateT.set s₁; StateT.set s₂) = StateT.set (m := m) s₂ := by
  unfold StateT.set StateT.instMonad StateT.bind
  simp only [bind_pure_comp, map_pure]

@[simp]
theorem get_set {s : σ} : (do StateT.set (m := m) s; StateT.get) = (do StateT.set s; pure s) := by
  unfold StateT.get StateT.instMonad StateT.bind StateT.set StateT.pure
  simp only [bind_pure_comp, map_pure]

@[simp]
theorem set_get : (do let s ← @StateT.get σ m _; StateT.set s) = pure ⟨⟩ := by
  unfold StateT.get StateT.instMonad StateT.bind StateT.set StateT.pure
  simp only [bind_pure_comp, map_pure]

instance : LawfulMonadStateOf σ (StateT σ m) where
  modifyGet_eq f := by
    simp only [MonadStateOf.modifyGet, modifyGet_eq_monadState, pure, MonadStateOf.get, set]
  get_get := by
    intro α a
    simp only [MonadStateOf.get, get_get]
  set_set := by
    intro s₁ s₂
    simp only [set, set_set]
  get_set := by
    intro s
    simp only [set, MonadStateOf.get, get_set, pure]
  set_get := by
    simp only [MonadStateOf.get, set, set_get, pure]

instance : LawfulMonadState σ (StateT σ m) := inferInstance

end StateT
