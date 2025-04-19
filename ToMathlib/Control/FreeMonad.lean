
/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import ToMathlib.Control.MonadHom
import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Free Monad of a Polynomial Functor

We define the free monad on a **polynomial functor** (`PFunctor`).

This file also contains the definition of the free monad on an _arbitrary_ mapping `f : Type u → Type v`.
This has the undesirable property of raising the universe level by 1, which means we can't pass
a `FreeMonad f` object as a continuation into an interactive protocol.
-/

universe u v w

namespace PFunctor

/-- The free monad on a polynomial functor.
This extends the `W`-type construction with an extra `pure` constructor. -/
inductive FreeM (P : PFunctor.{u}) : Type v → Type (max u v)
  | pure {α} (x : α) : FreeM P α
  | roll {α} (a : P.A) (r : P.B a → FreeM P α) : FreeM P α
deriving Inhabited

namespace FreeM

variable {P : PFunctor.{u}} {α β γ : Type u}

/-- Lift an object of the base polynomial functor into the free monad. -/
@[always_inline, inline]
def lift (x : P.Obj α) : FreeM P α := FreeM.roll x.1 (fun y ↦ FreeM.pure (x.2 y))

/-- Bind operator on `FreeM P` operation used in the monad definition. -/
@[always_inline, inline]
protected def bind : FreeM P α → (α → FreeM P β) → FreeM P β
  | FreeM.pure x, g => g x
  | FreeM.roll x r, g => FreeM.roll x (λ u ↦ FreeM.bind (r u) g)

@[simp]
lemma bind_pure (x : α) (r : α → FreeM P β) :
    FreeM.bind (FreeM.pure x) r = r x := rfl

@[simp]
lemma bind_roll (a : P.A) (r : P.B a → FreeM P β) (g : β → FreeM P γ) :
    FreeM.bind (FreeM.roll a r) g = FreeM.roll a (λ u ↦ FreeM.bind (r u) g) := rfl

@[simp]
lemma bind_lift (x : P.Obj α) (r : α → FreeM P β) :
    FreeM.bind (FreeM.lift x) r = FreeM.roll x.1 (fun a ↦ r (x.2 a)) := rfl

instance : Monad (FreeM P) where
  pure := FreeM.pure
  bind := FreeM.bind

@[simp]
lemma monad_pure_def (x : α) : (pure x : FreeM P α) = FreeM.pure x := rfl

@[simp]
lemma monad_bind_def (x : FreeM P α) (g : α → FreeM P β) :
    x >>= g = FreeM.bind x g := rfl

instance : LawfulMonad (FreeM P) :=
  LawfulMonad.mk' (FreeM P)
    (λ x ↦ by
      induction' x with α a _ h
      · rfl
      · refine congr_arg (FreeM.roll a) (funext λ i ↦ h i))
    (λ x f ↦ rfl)
    (λ x f g ↦ by
      induction' x with α a _ h
      · rfl
      · exact congr_arg (FreeM.roll a) (funext λ i ↦ h i))

/-- Proving a predicate `C` of `FreeM P α` requires two cases:
* `pure x` for some `x : α`
* `roll x r h` for some `x : P.A`, `r : P.B x → FreeM P α`, and `h : ∀ y, C (r y)`
Note that we can't use `Sort v` instead of `Prop` due to universe levels.-/
@[elab_as_elim]
protected def inductionOn {C : FreeM P α → Prop}
    (pure : ∀ x, C (pure x))
    (roll : (x : P.A) → (r : P.B x → FreeM P α) → (∀ y, C (r y)) → C (FreeM.roll x r)) :
    (oa : FreeM P α) → C oa
  | FreeM.pure x => pure x
  | FreeM.roll x r => roll x _ (λ u ↦ FreeM.inductionOn pure roll (r u))

section construct

/-- Shoulde be possible to unify with the above-/
@[elab_as_elim]
protected def construct {C : FreeM P α → Type*}
    (pure : (x : α) → C (pure x))
    (roll : (x : P.A) → (r : P.B x → FreeM P α) → ((y : P.B x) → C (r y)) → C (FreeM.roll x r)) :
    (oa : FreeM P α) → C oa
  | .pure x => pure x
  | .roll x r => roll x _ (λ u ↦ FreeM.construct pure roll (r u))

variable {C : FreeM P α → Type*} (h_pure : (x : α) → C (pure x))
  (h_roll : (x : P.A) → (r : P.B x → FreeM P α) → ((y : P.B x) → C (r y)) → C (FreeM.roll x r))

@[simp]
lemma construct_pure (y : α) : FreeM.construct h_pure h_roll (pure y) = h_pure y := rfl

@[simp]
lemma construct_roll (x : P.A) (r : P.B x → FreeM P α) :
    (FreeM.construct h_pure h_roll (FreeM.roll x r) : C (FreeM.roll x r)) =
      (h_roll x r (λ u ↦ FreeM.construct h_pure h_roll (r u))) := rfl

end construct

section mapM

variable {m : Type u → Type w}

/-- Canonical mapping of `FreeM P` into any other monad, given a map `s : (a : P.A) → m (P.B a)`. -/
protected def mapM [Pure m] [Bind m] (s : (a : P.A) → m (P.B a)) : FreeM P α → m α
  | .pure a => Pure.pure a
  | .roll a r => (s a) >>= (λ u ↦ (r u).mapM s)

-- protected def mapMHom [inst : Pure m] [Bind m] (s : (a : P.A) → m (P.B a)) :
--     (oa : FreeM P α) → m α
--   | FreeM.pure a => inst.pure a
--   | FreeM.roll a r => (s a) >>= (λ u ↦ (r u).mapM_aux s)

/-- `FreeM.mapM` as a monad homomorphism. -/
protected def mapMHom [Monad m] [LawfulMonad m] (s : (a : P.A) → m (P.B a)) : FreeM P →ᵐ m where
  toFun := FreeM.mapM s
  toFun_pure' x := rfl
  toFun_bind' x y := by
    induction x using FreeM.inductionOn with
    | pure x => simp [FreeM.mapM]
    | roll x r h => simp at h; simp [FreeM.mapM, h]

@[simp]
lemma mapM_lift [Monad m] [LawfulMonad m] (s : (a : P.A) → m (P.B a)) (x : P.Obj α) :
    FreeM.mapM s (FreeM.lift x) = s x.1 >>= (λ u ↦ (pure (x.2 u)).mapM s) := by
  simp [FreeM.mapM, FreeM.lift]

variable [Monad m] (s : (a : P.A) → m (P.B a))

@[simp]
lemma mapM_pure (x : α) : (FreeM.pure x : FreeM P α).mapM s = Pure.pure x := rfl

@[simp]
lemma mapM_roll (x : P.A) (r : P.B x → FreeM P α) :
    (FreeM.roll x r).mapM s = s x >>= λ u ↦ (r u).mapM s := rfl

end mapM

end FreeM

end PFunctor

/-- The free monad on a functor `f` is the type freely generated by values of type `f α`
and the operations `pure` and `bind`. Implemented directly rather than as a quotient.
Slightly different than constructions of free monads in Haskell because of universe issues. -/
inductive FreeMonad (f : Type u → Type v) (α : Type w) : Type (max (u + 1) v w)
  | protected pure (x : α) : FreeMonad f α
  | roll {β : Type u} (x : f β) (r : β → FreeMonad f α) : FreeMonad f α

namespace FreeMonad

variable {f : Type u → Type v} {α β γ : Type u}

/-- Lift an element of the base functor to the free monad by directly returning the result. -/
@[always_inline, inline]
def lift (x : f α) : FreeMonad f α := FreeMonad.roll x FreeMonad.pure

instance : MonadLift f (FreeMonad f) where
  monadLift x := FreeMonad.lift x

@[simp]
lemma monadLift_eq_lift (x : f α) :
  (x : FreeMonad f α) = FreeMonad.lift x := rfl

instance [Inhabited (f α)] : Inhabited (FreeMonad f α) := ⟨FreeMonad.lift default⟩

/-- Bind operator on `OracleComp spec` operation used in the monad definition. -/
@[always_inline, inline]
protected def bind : FreeMonad f α → (α → FreeMonad f β) → FreeMonad f β
  | FreeMonad.pure x, g => g x
  | FreeMonad.roll x r, g => FreeMonad.roll x (λ u ↦ FreeMonad.bind (r u) g)

@[simp]
lemma bind_pure (x : α) (r : α → FreeMonad f β) :
    FreeMonad.bind (FreeMonad.pure x) r = r x := rfl

@[simp]
lemma bind_roll (x : f α) (r : α → FreeMonad f β) (g : β → FreeMonad f γ) :
    FreeMonad.bind (FreeMonad.roll x r) g = FreeMonad.roll x (λ u ↦ FreeMonad.bind (r u) g) := rfl

@[simp]
lemma bind_lift (x : f α) (r : α → FreeMonad f β) :
    FreeMonad.bind (FreeMonad.lift x) r = FreeMonad.roll x r := rfl

instance : Monad (FreeMonad f) where
  pure := FreeMonad.pure
  bind := FreeMonad.bind

@[simp]
lemma monad_pure_def (x : α) : (pure x : FreeMonad f α) = FreeMonad.pure x := rfl

@[simp]
lemma monad_bind_def (x : FreeMonad f α) (g : α → FreeMonad f β) :
    x >>= g = FreeMonad.bind x g := rfl

instance : LawfulMonad (FreeMonad f) :=
  LawfulMonad.mk' (FreeMonad f)
    (λ x ↦ by
      induction' x with α x g r hr
      · rfl
      · exact congr_arg (FreeMonad.roll g) (funext λ u ↦ hr u))
    (λ x f ↦ rfl)
    (λ x f g ↦ by
      induction' x with α x g r hr
      · rfl
      · exact congr_arg (FreeMonad.roll g) (funext λ u ↦ hr u))

instance : MonadFunctor f (FreeMonad f) where
  monadMap g
    | FreeMonad.pure x => FreeMonad.pure x
    | FreeMonad.roll x r => g x >>= r

/-- Proving something about `FreeMonad f α` only requires two cases:
* `pure x` for some `x : α`
Note that we can't use `Sort v` instead of `Prop` due to universe levels.-/
@[elab_as_elim]
protected def inductionOn {C : FreeMonad f α → Prop}
    (pure : ∀ x, C (pure x))
    (roll : ∀ {β} (x : f β), (r : β → FreeMonad f α) →
      (∀ y, C (r y)) → C (x >>= r)) :
    (oa : FreeMonad f α) → C oa
  | FreeMonad.pure x => pure x
  | FreeMonad.roll x r => roll x _ (λ u ↦
      FreeMonad.inductionOn pure roll (r u))

section construct

/-- Shoulde be possible to unify with the above-/
@[elab_as_elim]
protected def construct {C : FreeMonad f α → Type*}
    (pure : (x : α) → C (pure x))
    (roll : {β : Type u} → (x : f β) → (r : β → FreeMonad f α) →
      ((y : β) → C (r y)) → C (x >>= r)) :
    (oa : FreeMonad f α) → C oa
  | .pure x => pure x
  | .roll x r => roll x _ (λ u ↦ FreeMonad.construct pure roll (r u))

variable {C : FreeMonad f α → Type*} (h_pure : (x : α) → C (pure x))
  (h_roll : {β : Type u} → (x : f β) → (r : β → FreeMonad f α) →
    ((y : β) → C (r y)) → C (x >>= r))

@[simp]
lemma construct_pure (y : α) : FreeMonad.construct h_pure h_roll (pure y) = h_pure y := rfl

@[simp]
lemma construct_roll (x : f β) (r : β → FreeMonad f α) :
    (FreeMonad.construct h_pure h_roll (roll x r) : C (roll x r)) =
      (h_roll x r (λ u ↦ FreeMonad.construct h_pure h_roll (r u))) := rfl

end construct

section mapM

variable {m : Type u → Type w} (s : {α : Type u} → f α → m α)

protected def mapM_aux [Pure m] [Bind m] (s : {α : Type u} → f α → m α) :
    (oa : FreeMonad f α) → m α
  | .pure x => pure x
  | .roll x r => s x >>= λ u ↦ (r u).mapM_aux s

protected def mapM' (m : Type u → Type w) [Monad m] [LawfulMonad m]
    (s : {α : Type u} → f α → m α) : FreeMonad f →ᵐ m where
  toFun := FreeMonad.mapM_aux s
  toFun_pure' x := rfl
  toFun_bind' x y := by
    induction x using FreeMonad.inductionOn with
    | pure x => simp [FreeMonad.mapM_aux]
    | roll x r h => simp at h; simp [FreeMonad.mapM_aux, h]

@[simp]
lemma mapM'_lift [Monad m] [LawfulMonad m]
    (s : {α : Type u} → f α → m α) (x : f α) :
    FreeMonad.mapM' m s (FreeMonad.lift x) = s x := by
  simp [FreeMonad.mapM', FreeMonad.lift, FreeMonad.mapM_aux]

/-- Canonical mapping of a free monad into any other monad, given a map on the base functor, -/
protected def mapM [Pure m] [Bind m] :
    (oa : FreeMonad f α) → (s : {α : Type u} → f α → m α) → m α
  | .pure x, _ => pure x
  | .roll x r, s => s x >>= λ u ↦ (r u).mapM s

variable [Monad m]

@[simp]
lemma mapM_pure (x : α) : (FreeMonad.pure x : FreeMonad f α).mapM s = pure x := rfl

-- @[simp]
-- lemma mapM'_pure (x : α) : (FreeMonad.pure x : FreeMonad f α).mapM' s = pure x := rfl

@[simp]
lemma mapM_roll (x : f α) (r : α → FreeMonad f β) :
    (FreeMonad.roll x r).mapM s = s x >>= λ u ↦ (r u).mapM s := rfl

end mapM

-- instance instMonadAlgebra {f} {pre : {α : Type v} → f α → α} : MonadAlgebra (FreeMonad f) where
--   monadAlg
--   | FreeMonad.pure x => x
--   | FreeMonad.roll x r => @instMonadAlgebra.monadAlg _ (r (pre x))

-- def prePostFree {f} {α β} (pre : α → Prop) (post : α × β → Prop) : FreeMonad f Prop → Prop
--   | FreeMonad.pure x => x
--   | FreeMonad.roll x r => ∃ inp, pre inp ∧ ∀ out, post (inp, out) → prePostFree pre post (r out)

end FreeMonad
