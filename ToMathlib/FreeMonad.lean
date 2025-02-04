
/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Data.Finset.Card
import Mathlib.Control.Lawful
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Data.Fintype.Card

/-!
# Free Monad of a Functor
-/

universe u v w

/-- The free monad on a functor `f` is the type freely generated by values of type `f α`
and the operations `pure` and `bind`. Implemented directly rather than as a quotient.
Slightly different than constructions of free monads in Haskell because of universe issues. -/
inductive FreeMonad (f : Type v → Type w) (α : Type u) : Type (max u (v + 1) w)
  | protected pure (x : α) : FreeMonad f α
  | roll {β : Type v} (x : f β) (r : β → FreeMonad f α) : FreeMonad f α

namespace FreeMonad

variable {f : Type v → Type w} {α β γ : Type v}

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

universe z

/-- Shoulde be possible to unify with the above-/
@[elab_as_elim]
protected def construct {C : FreeMonad f α → Type z}
    (pure : (x : α) → C (pure x))
    (roll : {β : Type v} → (x : f β) → (r : β → FreeMonad f α) →
      ((y : β) → C (r y)) → C (x >>= r)) :
    (oa : FreeMonad f α) → C oa
  | FreeMonad.pure x => pure x
  | FreeMonad.roll x r => roll x _ (λ u ↦
      FreeMonad.construct pure roll (r u))

variable {C : FreeMonad f α → Type z} (h_pure : (x : α) → C (pure x))
  (h_roll : {β : Type v} → (x : f β) → (r : β → FreeMonad f α) →
    ((y : β) → C (r y)) → C (x >>= r))

@[simp]
lemma construct_pure (y : α) : FreeMonad.construct h_pure h_roll (pure y) = h_pure y := rfl

@[simp]
lemma construct_roll (x : f β) (r : β → FreeMonad f α) :
    (FreeMonad.construct h_pure h_roll (roll x r) : C (roll x r)) =
      (h_roll x r (λ u ↦ FreeMonad.construct h_pure h_roll (r u))) := rfl

end construct

section mapM

variable {m : Type v → Type w} [Monad m] (s : {α : Type v} → f α → m α)

/-- Canonical mapping of a free monad into any other monad, given a map on the base functor, -/
protected def mapM (s : {α : Type v} → f α → m α) : (oa : FreeMonad f α) → m α
  | FreeMonad.pure x => pure x
  | FreeMonad.roll x r => s x >>= λ u ↦ (r u).mapM s

@[simp]
lemma mapM_pure (x : α) : (FreeMonad.pure x : FreeMonad f α).mapM s = pure x := rfl

@[simp]
lemma mapM_roll (x : f α) (r : α → FreeMonad f β) :
    (FreeMonad.roll x r).mapM s = s x >>= λ u ↦ (r u).mapM s := rfl

end mapM

end FreeMonad

section AlternativeMonad

-- TODO: maybe shouldn't actually extend both base types
class AlternativeMonad (m : Type u → Type v) extends Monad m, Alternative m where
  failure_bind {α β : Type u} (g : α → m β) : failure >>= g = failure

variable {m : Type u → Type v} [AlternativeMonad m] {α β : Type u}

@[simp] lemma failure_bind (g : α → m β) : (failure : m α) >>= g = failure :=
  AlternativeMonad.failure_bind g

@[simp] lemma map_failure [LawfulMonad m] (g : α → β) : g <$> (failure : m α) = failure := by
  rw [map_eq_bind_pure_comp, failure_bind]

@[simp] lemma failure_seq [LawfulMonad m] (ob : m α) : (failure : m (α → β)) <*> ob = failure := by
  rw [seq_eq_bind_map, failure_bind]

end AlternativeMonad

section PMF

variable {α β : Type u}

@[simp]
lemma PMF.monad_pure_eq_pure (x : α) : (Pure.pure x : PMF α) = PMF.pure x := rfl

@[simp]
lemma PMF.monad_bind_eq_bind (p : PMF α) (q : α → PMF β) :
    p >>= q = p.bind q := rfl

end PMF

namespace OptionT

@[simp]
lemma run_failure {α : Type u} {m : Type u → Type v} [Monad m] :
    (failure : OptionT m α).run = pure none := rfl

instance : AlternativeMonad Option where
  failure_bind _ := rfl
  __ := instAlternativeOption
  __ := instMonadOption

instance (m : Type u → Type v) [Monad m] [LawfulMonad m] : AlternativeMonad (OptionT m) where
  failure_bind {α β} g := OptionT.ext_iff.mpr <|
    by simp only [OptionT.run_bind, OptionT.run_failure, pure_bind]
  __ := OptionT.instAlternative
  __ := OptionT.instMonad

lemma liftM_def {m : Type u → Type v} [Monad m] {α : Type u}
    (x : m α) : (x : OptionT m α) = OptionT.lift x := rfl

end OptionT

namespace StateT

variable {m : Type u → Type v} {m' : Type u → Type w}
  {σ α β : Type u}

instance [MonadLift m m'] : MonadLift (StateT σ m) (StateT σ m') where
  monadLift x := StateT.mk fun s => liftM ((x.run) s)

@[simp]
lemma liftM_of_liftM_eq [MonadLift m m'] (x : StateT σ m α) :
    (liftM x : StateT σ m' α) = StateT.mk fun s => liftM (x.run s) := rfl

lemma liftM_def [Monad m] (x : m α) : (x : StateT σ m α) = StateT.lift x := rfl

-- TODO: should this be simp?
lemma monad_pure_def [Monad m] (x : α) :
    (pure x : StateT σ m α) = StateT.pure x := rfl

lemma monad_failure_def [Monad m] [Alternative m] :
    (failure : StateT σ m α) = StateT.failure := rfl

@[simp]
lemma run_failure [Monad m] [Alternative m] (s : σ) :
    (StateT.failure : StateT σ m α).run s = failure := rfl

@[simp]
lemma mk_eq_pure [Monad m] (x : α) :
  StateT.mk (λ s ↦ pure (x, s)) = (pure x : StateT σ m α) := rfl

@[simp]
lemma lift_failure [AlternativeMonad m] :
    (StateT.lift (failure : m α) : StateT σ m α) = failure := by
  refine StateT.ext fun s ↦ ?_
  simp [StateT.failure, monad_failure_def]

end StateT

lemma list_mapM_loop_eq {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α β : Type u} (xs : List α) (f : α → m β) (ys : List β) :
    List.mapM.loop f xs ys = (ys.reverse ++ ·) <$> List.mapM.loop f xs [] := by
  revert ys
  induction xs with
  | nil => simp [List.mapM.loop]
  | cons x xs h =>
      intro ys
      simp only [List.mapM.loop, map_bind]
      refine congr_arg (f x >>= ·) (funext λ x ↦ ?_)
      simp [h (x :: ys), h [x]]
