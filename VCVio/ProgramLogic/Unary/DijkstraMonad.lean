/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Control.Monad.Basic
import Mathlib.Control.Monad.Cont
import Mathlib.CategoryTheory.Monad.Basic
import ToMathlib.Control

/-!
# Dijkstra monad

This file aims to formalize the content of the paper
[Dijkstra monads for all](https://dl.acm.org/doi/pdf/10.1145/3341708).

-/

universe u v w z

class DijkstraMonad (w : Type u → Type v) (d : {α : Type u} → w α → Type z) [Monad w] where
  -- d {α : Type u} : w α → Type z
  dPure {α : Type u} : (x : α) → d (pure x)
  dBind {α β : Type u} {wa : w α} {wb : α → w β} : d wa → ((a : α) → d (wb a)) → d (wa >>= wb)

export DijkstraMonad (dPure dBind)

infixl:55  " >>=ᵈ " => DijkstraMonad.dBind

class LawfulDijkstraMonad (w : Type u → Type v) (d : {α : Type u} → w α → Type z) [Monad w]
    [LawfulMonad w] [DijkstraMonad w d] where
  dPure_dBind {α : Type u} {a : w α} (m : d a) : cast (congrArg _ (bind_pure a)) (m >>=ᵈ dPure) = m
  dBind_dPure_comp {α β : Type u} (f : α → w β) : sorry
  dBind_assoc {α β γ : Type u} (wa : w α) (wb : α → w β) (wc : β → w γ) :
    sorry
    -- dBind (wa >>= wb) wc = dBind wa (fun a => dBind (wb a) wc)

class DijkstraMonadMorphism (w₁ : Type u → Type v) (w₂ : Type u → Type w)
    (d₁ : {α : Type u} → w₁ α → Type z) (d₂ : {α : Type u} → w₂ α → Type z)
    [Monad w₁] [Monad w₂] [MonadLift w₁ w₂] [DijkstraMonad w₁ d₁] [DijkstraMonad w₂ d₂] where
  dMap {α : Type u} {a : w₁ α} : d₁ a → d₂ (liftM a)

class LawfulDijkstraMonadMorphism (w₁ : Type u → Type v) (w₂ : Type u → Type w)
    (d₁ : {α : Type u} → w₁ α → Type z) (d₂ : {α : Type u} → w₂ α → Type z)
    [Monad w₁] [Monad w₂] [MonadLift w₁ w₂] [DijkstraMonad w₁ d₁] [DijkstraMonad w₂ d₂]
    [DijkstraMonadMorphism w₁ w₂ d₁ d₂]
    [LawfulMonad w₁] [LawfulMonad w₂] [LawfulMonadLift w₁ w₂] where
  -- dMap_dPure {α : Type u} {a : w₁ α} : dMap (dPure a) = dPure (liftM a)
  -- dMap_dBind {α β : Type u} {a : w₁ α} {b : α → w₁ β} {x : d₁ a} {f : (a : α) → d₁ (b a)} :

variable {m : Type u → Type v} {n : Type u → Type w}

instance [Monad m] [Monad n] [MonadRelation m n] :
    DijkstraMonad n (fun na => { ma : m _ // monadRel ma na}) where
  dPure := sorry
  dBind := sorry
