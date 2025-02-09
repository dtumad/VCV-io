/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Lawful.MonadLift

/-! # Monad relations -/

universe u v w

class MonadRelation (m : Type u → Type v) (n : Type u → Type w) where
  monadRel {α : Type u} : m α → n α → Prop

export MonadRelation (monadRel)

namespace MonadRelation

scoped infix:50 " ∼ₘ " => monadRel

end MonadRelation

class LawfulMonadRelation (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [MonadRelation m n] where
  pure_rel {α : Type u} (a : α) : monadRel (pure a : m α) (pure a : n α)
  bind_rel {α β : Type u} {ma : m α} {mb : α → m β} {na : n α} {nb : α → n β}
    (ha : monadRel ma na) (hb : ∀ a, monadRel (mb a) (nb a)) : monadRel (ma >>= mb) (na >>= nb)

export LawfulMonadRelation (pure_rel bind_rel)

attribute [simp] pure_rel bind_rel

-- TODO: add examples & interactions with other monad classes

/-- A (transitive) monad lift defines a monad relation via its graph -/
instance {m n} [MonadLiftT m n] : MonadRelation m n where
  monadRel := fun ma na => liftM ma = na

/-- A (transitive) lawful monad lift defines a lawful monad relation via its graph -/
instance {m n} [Monad m] [Monad n] [MonadLiftT m n] [LawfulMonadLiftT m n] :
    LawfulMonadRelation m n where
  pure_rel _ := by simp only [monadRel, liftM_pure]
  bind_rel _ _ := by simp_all only [monadRel, ← liftM_bind]
