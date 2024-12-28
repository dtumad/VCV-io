
/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Data.Finset.Card
import Mathlib.Control.Lawful

universe u v w

/-- The free monad on a functor `f` is the type freely generated by values of type `f α`
and the operations `pure` and `bind`. Implemented directly rather than as a quotient.
Slightly different than constructions of free monads in Haskell because of universe issues. -/
inductive FreeMonad (f : Type u → Type u) : Type u → Type (u + 1)
  | protected pure {α : Type u} (x : α) : FreeMonad f α
  | roll {α β : Type u} (x : f α) (r : α → FreeMonad f β) : FreeMonad f β

namespace FreeMonad

variable {f : Type u → Type u} {α β : Type u}

/-- Lift an element of the base functor to the free monad by directly returning the result. -/
def lift (x : f α) : FreeMonad f α :=
  FreeMonad.roll x FreeMonad.pure

/-- Bind operator on `OracleComp spec` operation used in the monad definition. -/
protected def bind : FreeMonad f α → (α → FreeMonad f β) → FreeMonad f β
  | FreeMonad.pure x, g => g x
  | FreeMonad.roll x r, g => FreeMonad.roll x (λ u ↦ FreeMonad.bind (r u) g)

instance : Monad (FreeMonad f) where
  pure := FreeMonad.pure
  bind := FreeMonad.bind

lemma pure_def (x : α) : (pure x : FreeMonad f α) = FreeMonad.pure x := rfl

lemma bind_def (x : FreeMonad f α) (g : α → FreeMonad f β) :
    x >>= g = FreeMonad.bind x g := rfl

instance : LawfulMonad (FreeMonad f) :=
  LawfulMonad.mk' (FreeMonad f)
    (λ x ↦ by
      induction' x with α x α β g r hr
      · rfl
      · exact congr_arg (FreeMonad.roll g) (funext λ u ↦ hr u))
    (λ x f ↦ rfl)
    (λ x f g ↦ by
      induction' x with α x α β g r hr
      · rfl
      · exact congr_arg (FreeMonad.roll g) (funext λ u ↦ hr u _))

/-- Proving something about `FreeMonad f α` only requires two cases:
* `pure x` for some `x : α`
Note that we can't use `Sort v` instead of `Prop` due to universe levels.-/
@[elab_as_elim]
protected def inductionOn {C : FreeMonad f α → Prop}
    (pure : ∀ x, C (pure x))
    (roll : ∀ {β} (x : f β), (r : β → FreeMonad f α) →
      (∀ y, C (r y)) → C (FreeMonad.lift x >>= r)) :
    (oa : FreeMonad f α) → C oa
  | FreeMonad.pure x => pure x
  | FreeMonad.roll x r => roll x _ (λ u ↦
      FreeMonad.inductionOn pure roll (r u))

/-- Canonical mapping of a free monad into any other monad, given a map on the base functor -/
protected def mapM {m : Type u → Type v} [Monad m]
    (s : {α : Type u} → f α → m α) :
    (oa : FreeMonad f α) → m α
  | FreeMonad.pure x => pure x
  | FreeMonad.roll x r => (s x >>= λ u ↦ (r u).mapM s)

end FreeMonad

#check Option.getM

def OptionT.mapM {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n] [Alternative n]
    {α : Type u} (f : {α : Type u} → m α → n α) : OptionT m α → n α := by
  refine λ x ↦ f x.run >>= Option.getM
