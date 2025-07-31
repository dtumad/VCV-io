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
def IsCommutativeAt (m : Type u → Type v) [Monad m] {α β : Type u} (ma : m α) (mb : m β) : Prop :=
  (do let a ← ma; let b ← mb; pure (a, b)) = (do let b ← mb; let a ← ma; pure (a, b))

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
  -- Use associativity to factor out the pair construction
  have h1 : (ma >>= fun a => mb >>= fun b => f (a, b)) =
           ((ma >>= fun a => mb >>= fun b => pure (a, b)) >>= fun ⟨a, b⟩ => f (a, b)) := by
    simp only [bind_assoc, pure_bind]
  have h2 : (mb >>= fun b => ma >>= fun a => f (a, b)) =
           ((mb >>= fun b => ma >>= fun a => pure (b, a)) >>= fun ⟨b, a⟩ => f (a, b)) := by
    simp only [bind_assoc, pure_bind]
  rw [h1, h2]
  -- Apply commutativity
  rw [bind_comm]
  simp_all

@[simp] theorem IsCommutativeAt.bind_comm {m} [Monad m] [LawfulMonad m] {α β}
    (ma : m α) (mb : m β) (h : IsCommutativeAt m ma mb) :
      (ma >>= fun a => mb >>= fun b => pure (a, b)) =
        (mb >>= fun b => ma >>= fun a => pure (a, b)) :=
  h

-- The main commutativity lemma for composed computations
@[simp] theorem IsCommutativeAt.bind_comm_comp {m} [Monad m] [LawfulMonad m] {α β γ}
    (ma : m α) (mb : m β) (h : IsCommutativeAt m ma mb) (f : α × β → m γ) :
      (ma >>= fun a => mb >>= fun b => f (a, b)) = (mb >>= fun b => ma >>= fun a => f (a, b)) := by
  -- Use associativity to factor out the pair construction
  have h1 : (ma >>= fun a => mb >>= fun b => f (a, b)) =
           ((ma >>= fun a => mb >>= fun b => pure (a, b)) >>= fun ⟨a, b⟩ => f (a, b)) := by
    simp only [bind_assoc, pure_bind]
  have h2 : (mb >>= fun b => ma >>= fun a => f (a, b)) =
           ((mb >>= fun b => ma >>= fun a => pure (b, a)) >>= fun ⟨b, a⟩ => f (a, b)) := by
    simp only [bind_assoc, pure_bind]
  rw [h1, h2]
  -- Apply commutativity
  rw [h]
  simp_all

-- Commutativity extends to sequences of three operations
theorem bind_comm_triple {m} [Monad m] [LawfulMonad m] [IsCommutative m] {α β γ δ}
    (ma : m α) (mb : m β) (mc : m γ) (f : α × β × γ → m δ) :
    (ma >>= fun a => mb >>= fun b => mc >>= fun c => f (a, b, c)) =
    (mb >>= fun b => ma >>= fun a => mc >>= fun c => f (a, b, c)) :=
  bind_comm_comp ma mb (fun p => mc >>= fun c => f (p.1, p.2, c))

-- -- Commutative monads allow reordering of independent computations
-- theorem bind_reverse_triple {m} [Monad m] [LawfulMonad m] [IsCommutative m] {α β γ δ}
--     (ma : m α) (mb : m β) (mc : m γ) (f : α × β × γ → m δ) :
--     (ma >>= fun a => mb >>= fun b => mc >>= fun c => f (a, b, c)) =
--     (mc >>= fun c => mb >>= fun b => ma >>= fun a => f (a, b, c)) := by
--   -- First swap a and b
--   rw [bind_comm_triple]
--   -- Then swap (b,a) with c by treating (b,a) as a single unit
--   rw [bind_comm_comp (mb >>= fun b => ma >>= fun a => pure (a, b)) mc
--       (fun p => f p.1 p.2)]

/-- The identity monad is commutative -/
instance : IsCommutative Id where
  bind_comm := fun _ _ => rfl

/-- The option monad is commutative -/
instance : IsCommutative Option where
  bind_comm := fun ma mb => by cases ma <;> cases mb <;> rfl

/-- The reader monad is commutative -/
instance {ρ} {m} [Monad m] [IsCommutative m] : IsCommutative (ReaderT ρ m) where
  bind_comm := fun ma mb => by sorry

end Monad
