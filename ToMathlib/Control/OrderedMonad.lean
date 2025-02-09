/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Control.Monad.Cont
import Mathlib.CategoryTheory.Monad.Basic
import ToMathlib.Control.MonadAlgebra
import ToMathlib.Control.MonadRelation
import ToMathlib.Control.MonadTransformer
import Mathlib.Order.Monotone.Basic

/-!
# Ordered monads

This file collects all definitions and basic theorems about adding ordering to monads.

## Main definitions

- `OrderedMonad`
- `OrderedMonadAlgebra`
- `OrderedMonadLift`
- `MonadIdeal`
- `OrderedMonadTransformer`
- Left / right Kan extension of ordered monads

-/

universe u v w

section Prelude

/-- `pointwiseRelation r f g` is the pullback of a relation `r` on `β` to a relation on `α` via `f`
  and `g`. -/
def pointwiseRelation {α β : Type u} (r : β → β → Prop) (f g : α → β) : α → α → Prop :=
  fun a b => r (f a) (g b)

/-- `Proper R m` states that a value `m` respects the relation `R` by being related to itself.
This is useful for expressing that certain operations preserve relationships.

NOTE: this is a direct translation from Coq, the Lean version is essentially `IsRefl` -/
def Proper (A : Type u) (R : A → A → Prop) (m : A) : Prop := R m m

end Prelude

/-- An ordered monad `m` is a monad equipped with a preorder on each type `m α`, such that the bind
    operation preserves the order. -/
class OrderedMonad (m : Type u → Type v) extends Monad m where
  [monadOrder {α : Type u} : Preorder (m α)]
  bind_mono {α β : Type u} {ma ma' : m α} {f f' : α → m β} (ha : ma ≤ ma') (hf : ∀ a, f a ≤ f' a) :
    ma >>= f ≤ ma' >>= f'

export OrderedMonad (monadOrder bind_mono)

instance {m} [OrderedMonad m] {α : Type u} : Preorder (m α) := monadOrder

attribute [simp] bind_mono

/-- Unbundled version of `OrderedMonad`. -/
class Monad.IsOrdered (m : Type u → Type v) [Monad m] where
  [monadOrder {α : Type u} : Preorder (m α)]
  bind_mono {α β : Type u} {ma ma' : m α} {f f' : α → m β} (ha : ma ≤ ma') (hf : ∀ a, f a ≤ f' a) :
    ma >>= f ≤ ma' >>= f'

instance {m} [Monad m] [Monad.IsOrdered m] : OrderedMonad m where
  monadOrder := Monad.IsOrdered.monadOrder
  bind_mono := Monad.IsOrdered.bind_mono

namespace OrderedMonad

/-- The less-than-or-equal relation on an ordered monad `m`. -/
@[reducible] def monadLE {m} [OrderedMonad m] : {α : Type u} → m α → m α → Prop :=
  monadOrder.le

/-- The less-than relation on an ordered monad `m`. -/
@[reducible] def monadLT {m} [OrderedMonad m] : {α : Type u} → m α → m α → Prop :=
  monadOrder.lt

@[inherit_doc] scoped infix:50 " ≤ₘ " => OrderedMonad.monadLE
@[inherit_doc] scoped infix:50 " <ₘ " => OrderedMonad.monadLT

macro_rules | `($x ≤ₘ $y)  => `(binrel% OrderedMonad.monadLE $x $y)
macro_rules | `($x <ₘ $y)  => `(binrel% OrderedMonad.monadLT $x $y)

/-- Any monad can be given the discrete preorder, where `a ≤ b` if and only if `a = b`.

Note that this is the default instance for `OrderedMonad` on any monad. -/
instance instDiscreteMonad {m} [Monad m] : OrderedMonad m where
  monadOrder := {
    le := (. = .)
    le_refl _ := rfl
    le_trans _ _ _ _ _ := by simp_all
  }
  bind_mono h hf := by simp_all; rename_i f f'; have : f = f' := funext hf; simp [this]

end OrderedMonad

export OrderedMonad (monadLE monadLT)

open OrderedMonad

-- class OrderedAlgebra (m : Type u → Type u) [Monad m] [MonadAlgebra m] where
--   [carrierOrder {α : Type u} : Preorder α]
--   monadAlg_mono {α β : Type u} {f f' : α → β} {ma ma' : m α} (hf : ∀ a, (f a) ≤ (f' a))
--     (hm : ma ≤ ma') : (monadAlg (f <$> ma)) ≤ (monadAlg (f' <$> ma'))

class OrderedMonadAlgebra (m : Type u → Type v) [OrderedMonad m] [MonadAlgebra m] where
  [carrierOrder {α : Type u} : Preorder α]
  monadAlg_mono {α β : Type u} {f f' : α → β} {ma ma' : m α} (hf : ∀ a, (f a) ≤ (f' a))
    (hm : ma ≤ₘ ma') : (monadAlg (f <$> ma)) ≤ (monadAlg (f' <$> ma'))

export OrderedMonadAlgebra (monadAlg_mono)

attribute [simp] monadAlg_mono

section MonadLift

/-- A class that express an ordering for monad lifts. -/
class MonadLift.LE (m : Type u → Type v) (n : Type u → Type w) [Monad m] [OrderedMonad n]
    [φ : MonadLift m n] [ψ : MonadLift m n] where
  monadLift_le {α} (a : m α) : φ.monadLift a ≤ₘ ψ.monadLift a

/-- If the target monad `n` is ordered, then we have a preorder on the monad lifts from `m` to `n`.
  -/
instance {m n} [Monad m] [OrderedMonad n] : Preorder (MonadLift m n) where
  le := fun φ ψ => ∀ {α : Type u} (a : m α), φ.monadLift a ≤ₘ ψ.monadLift a
  le_refl _ := by intro α a; simp only [ge_iff_le, le_refl]
  le_trans φ₁ φ₂ φ₃ h1 h2 := by simp_all; intro α a; exact le_trans (h1 a) (h2 a)

class OrderedMonadLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [OrderedMonad m] [OrderedMonad n] extends MonadLift m n where
  monadLift_mono {α} : Monotone (@monadLift α)

class OrderedMonadLiftT (m : Type u → Type v) (n : Type u → Type w) [OrderedMonad m] [OrderedMonad n]
    extends MonadLiftT m n where
  monadLift_mono {α} : Monotone (@monadLift α)

export OrderedMonadLiftT (monadLift_mono)

attribute [simp] monadLift_mono

@[simp] theorem monadLift_mono' {m n} [OrderedMonad m] [OrderedMonad n] [OrderedMonadLiftT m n]
    {α} {a b : m α} (h : a ≤ₘ b) : monadLift a ≤ₘ (monadLift b : n α) :=
  (monadLift_mono (m := m) (n := n) (α := α)) h

instance {m} [OrderedMonad m] : OrderedMonadLiftT m m where
  monadLift_mono h := by simp only [monadLift_self, h]

-- TODO: fix synthesization order
-- instance (m n o) [Monad m] [Monad n] [Monad o] [OrderedMonadLift n o]
--     [OrderedMonadLiftT m n] : OrderedMonadLiftT m o where
--   monadLift_mono h := by simp

open OrderedMonad in
/-- Given the (default) discrete preorder on the beginning monad `m`, we can have a preorder on the
    monad lifts from `m` to `n`. -/
instance instDiscreteMonadLift {m n} [Monad m] [OrderedMonad n] [MonadLift m n] :
    OrderedMonadLift m n where
  monadLift_mono h := by rename_i a b; have : a = b := h; simp only [this, le_refl]

end MonadLift

section MonadRelation

open MonadRelation in
class MonadIdeal (m : Type u → Type v) (n : Type u → Type w) [Monad m] [OrderedMonad n] extends
    MonadRelation m n where
  monadRel_upper_closed {α} {ma : m α} {na na' : n α} (hr : ma ∼ₘ na) (hn : na ≤ₘ na') : ma ∼ₘ na'

instance {m n} [Monad m] [OrderedMonad n] [MonadLiftT m n] : MonadRelation m n where
  monadRel := fun a b => monadLift a ≤ₘ b

instance {m n} [Monad m] [OrderedMonad n] [MonadLiftT m n] [LawfulMonad m] [LawfulMonad n]
    [LawfulMonadLiftT m n] : LawfulMonadRelation m n where
  pure_rel := by simp [monadRel]
  bind_rel ha hb := by
    simp_all only [monadRel, ge_iff_le]
    rename_i ma mb na nb
    rw [← monadLift_bind]
    calc
      _ ≤ na >>= (fun x => monadLift (mb x)) := bind_mono ha (by simp)
      _ ≤ na >>= nb := bind_mono (le_of_eq rfl) hb

-- TODO: monad morphism also defines a monad ideal

end MonadRelation

class OrderedMonadTransformer (t : (Type u → Type v) → Type u → Type w) extends MonadTransformer t where
  mapOrderedMonad {m} [OrderedMonad m] : OrderedMonad (t m)
  liftOf_mono {m n} [OrderedMonad m] [OrderedMonad n] [OrderedMonadLiftT m n] :
    OrderedMonadLiftT (t m) (t n)

class AssertAssume (α : Type u) [Preorder α] where
  assert : Prop → α → α
  assume : Prop → α → α
  assert_strengthen : ∀ p x, assert p x ≤ x
  assume_weaken : ∀ p x, x ≤ assume p x
  assert_assume_iff : ∀ p x y, assert p x ≤ y ↔ x ≤ assume p y

section KanExtension
variable {w : Type u → Type v} [Monad w] [OrderedMonad w]

def leftKanExtension {α β : Type u} (f : w β) (p : w α) :=
  { ext : α → w β // p >>= ext ≤ₘ f ∧ (∀ w', p >>= w' ≤ₘ f → ∀ b, w' b ≤ₘ ext b) }

def rightKanExtension {α β : Type u} (f : w β) (p : w α) :=
  { ext : β → w α // f >>= ext ≤ₘ p ∧ (∀ w', f >>= w' ≤ₘ p → ∀ a, w' a ≤ₘ ext a) }

end KanExtension

section Examples

def WPure : Type u → Type u := fun α => {m : Cont Prop α // ∀ p p', (∀ a, p a → p' a) → m p → m p'}

#print WPure

noncomputable instance : Monad WPure where
  pure := fun a => ⟨pure a, fun p p' h => by aesop⟩
  bind := fun a f => ⟨a.1 >>= (fun a => (f a).1), fun p p' h => by simp_all [bind]; sorry⟩

#print instMonadWPure

noncomputable instance : LawfulMonad WPure := sorry

-- `W^Pure` in the paper
noncomputable instance : OrderedMonad WPure where
  monadOrder := {
    le := fun x y ↦ ∀ p, x.1 p → y.1 p
    le_refl := fun a => by simp
    le_trans := fun a b c h1 h2 => by simp_all
    lt_iff_le_not_le := sorry
  }
  bind_mono ha hf := by sorry
    -- apply ha
    -- have : ∀ i, f i p → f' i p := fun i => hf i p
    -- have : (fun i => f i p) = (fun i => f' i p) := by funext i; sorry
    -- revert h
    -- have : ∀ i, f i p = f' i p := by
    --   intro i
    --   simp_all [hf i p]
    -- simp [h, this]

-- `W^St` in the paper
noncomputable instance {σ : Type u} : OrderedMonad (StateT σ (Cont Prop)) where
  monadOrder := {
    le := fun x y ↦ ∀ p s, x p s → y p s
    lt := fun x y ↦ monadOrder.le x y ∧ ¬ monadOrder.le y x
    le_refl := sorry
    le_trans := sorry
    lt_iff_le_not_le := by sorry
  }
  bind_mono := sorry

-- instance : OrderedMonad (ReaderT σ (Cont Prop)) where
--   le := inferInstance
--   bind_mono := sorry

end Examples
