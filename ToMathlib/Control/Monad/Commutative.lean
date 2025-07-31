/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Monad.Hom

/-!
# Commutative monads
-/

universe u v

namespace Monad

/-- Two monadic actions `ma : m α` and `mb : m β` are commutative if the following holds:
```
(do let a ← ma; let b ← mb; pure (a, b)) = (do let b ← mb; let a ← ma; pure (a, b))
```
-/
class IsCommutativeAt (m : Type u → Type v) [Monad m] {α β : Type u} (ma : m α) (mb : m β) where
  bind_comm : (do let a ← ma; let b ← mb; pure (a, b)) = (do let b ← mb; let a ← ma; pure (a, b))

/-- A monad is commutative if any two monadic actions `ma : m α` and `mb : m β` can be applied
  in any order. In other words, the following holds:
```
(do let a ← ma; let b ← mb; pure (a, b)) = (do let b ← mb; let a ← ma; pure (a, b))
```
-/
class IsCommutative (m : Type u → Type v) [Monad m] where
  bind_comm {α β} (ma : m α) (mb : m β) : IsCommutativeAt m ma mb

export Monad.IsCommutative (bind_comm)

attribute [simp] bind_comm

-- Instance for accessing bind_comm directly
instance {m} [Monad m] [IsCommutative m] {α β} (ma : m α) (mb : m β) :
    IsCommutativeAt m ma mb := bind_comm ma mb

-- The main commutativity lemma for composed computations
@[simp] theorem bind_comm_comp {m} [Monad m] [LawfulMonad m] [IsCommutative m] {α β γ}
    (ma : m α) (mb : m β) (f : α × β → m γ) :
      (ma >>= fun a => mb >>= fun b => f (a, b)) = (mb >>= fun b => ma >>= fun a => f (a, b)) := by
  -- Factor out the composition using associativity
  have h1 : (ma >>= fun a => mb >>= fun b => f (a, b)) = 
           ((ma >>= fun a => mb >>= fun b => pure (a, b)) >>= fun p => f p.1 p.2) := by
    rw [bind_assoc]
    congr; ext a
    rw [bind_assoc]
    congr; ext b
    rw [pure_bind]
  have h2 : (mb >>= fun b => ma >>= fun a => f (a, b)) = 
           ((mb >>= fun b => ma >>= fun a => pure (b, a)) >>= fun p => f p.2 p.1) := by
    rw [bind_assoc]
    congr; ext b
    rw [bind_assoc]
    congr; ext a
    rw [pure_bind]
  rw [h1, h2]
  -- Apply commutativity and fix the order
  rw [IsCommutativeAt.bind_comm ma mb]
  congr; ext p
  congr
  · exact p.2 
  · exact p.1

-- Commutativity for pure results (simpler case)
@[simp] theorem bind_comm_pure {m} [Monad m] [IsCommutative m] {α β}
    (ma : m α) (mb : m β) :
    (do let a ← ma; let b ← mb; pure (a, b)) = (do let b ← mb; let a ← ma; pure (a, b)) :=
  IsCommutativeAt.bind_comm

-- Do notation version of bind_comm_comp
theorem do_bind_comm_comp {m} [Monad m] [LawfulMonad m] [IsCommutative m] {α β γ}
    (ma : m α) (mb : m β) (f : α × β → m γ) :
      (do let a ← ma; let b ← mb; f (a, b)) = (do let b ← mb; let a ← ma; f (a, b)) := by
  simp only [← bind_comm_comp]

-- Commutativity for mapping functions over the result
@[simp] theorem bind_comm_map {m} [Monad m] [LawfulMonad m] [IsCommutative m] {α β γ}
    (ma : m α) (mb : m β) (f : α × β → γ) :
    (ma >>= fun a => mb >>= fun b => pure (f (a, b))) = (mb >>= fun b => ma >>= fun a => pure (f (a, b))) :=
  bind_comm_comp ma mb (fun p => pure (f p.1 p.2))

-- Do notation version for mapping
theorem do_bind_comm_map {m} [Monad m] [LawfulMonad m] [IsCommutative m] {α β γ}
    (ma : m α) (mb : m β) (f : α × β → γ) :
    (do let a ← ma; let b ← mb; pure (f (a, b))) = (do let b ← mb; let a ← ma; pure (f (a, b))) := by
  simp only [← bind_comm_map]

-- Commutativity extends to sequences of three operations
theorem bind_comm_triple {m} [Monad m] [LawfulMonad m] [IsCommutative m] {α β γ δ}
    (ma : m α) (mb : m β) (mc : m γ) (f : α × β × γ → m δ) :
    (ma >>= fun a => mb >>= fun b => mc >>= fun c => f (a, b, c)) =
    (mb >>= fun b => ma >>= fun a => mc >>= fun c => f (a, b, c)) :=
  bind_comm_comp ma mb (fun p => mc >>= fun c => f p.1 p.2 c)

-- Do notation version for triple
theorem do_bind_comm_triple {m} [Monad m] [LawfulMonad m] [IsCommutative m] {α β γ δ}
    (ma : m α) (mb : m β) (mc : m γ) (f : α × β × γ → m δ) :
    (do let a ← ma; let b ← mb; let c ← mc; f (a, b, c)) =
    (do let b ← mb; let a ← ma; let c ← mc; f (a, b, c)) := by
  simp only [← bind_comm_triple]

-- Commutative monads allow reordering of independent computations
theorem bind_reorder {m} [Monad m] [LawfulMonad m] [IsCommutative m] {α β γ δ}
    (ma : m α) (mb : m β) (mc : m γ) (f : α × β × γ → m δ) :
    (ma >>= fun a => mb >>= fun b => mc >>= fun c => f (a, b, c)) =
    (mc >>= fun c => mb >>= fun b => ma >>= fun a => f (a, b, c)) := by
  -- First swap a and b
  rw [bind_comm_triple]
  -- Then swap (b,a) with c
  rw [bind_comm_comp]

-- Do notation version for reorder
theorem do_bind_reorder {m} [Monad m] [LawfulMonad m] [IsCommutative m] {α β γ δ}
    (ma : m α) (mb : m β) (mc : m γ) (f : α × β × γ → m δ) :
    (do let a ← ma; let b ← mb; let c ← mc; f (a, b, c)) =
    (do let c ← mc; let b ← mb; let a ← ma; f (a, b, c)) := by
  simp only [← bind_reorder]

-- Identity monad is commutative
instance : IsCommutative Id where
  bind_comm := fun ma mb => by
    constructor
    rfl

-- Option monad is commutative
instance : IsCommutative Option where
  bind_comm := fun ma mb => by
    constructor
    cases ma with
    | none => cases mb <;> rfl
    | some a =>
      cases mb with
      | none => rfl
      | some b => rfl

end Monad
