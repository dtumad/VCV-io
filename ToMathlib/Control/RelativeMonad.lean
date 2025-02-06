/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Relativeeased under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Control.Monad.Basic
import Mathlib.CategoryTheory.Monad.Basic

/-!
# Relative monad

-/

namespace CategoryTheory

open Category

universe v₁ u₁

-- morphism levels before object levels. See note [CategoryTheory universes].
variable (C D : Type u₁) [Category.{v₁} C] [Category.{v₁} D]

/-- The data of a **relative monad** over a functor `F : C ⟶ D` consists of:
- a map between objects `T : C → D`
- a natural transformation `η : ∀ {X}, F X ⟶ T X`
- a natural transformation `μ : ∀ {X Y}, (F X ⟶ T Y) ⟶ (T X ⟶ T Y)`
satisfying three equations:
- `μ_{X, X} ∘ η_X = 1_{T X}` (left unit)
- `∀ f, η_X ≫ μ_{X, Y} = f` (right unit)
- `∀ f g, μ_{X, Z} (f ≫ μ_{Y, Z} g) = μ_{X, Y} f ≫ μ_{Y, Z} g` (associativity)
-/
structure RelativeMonad extends C ⥤ D where
  /-- The "correction" mapping. -/
  T : C → D
  /-- The unit for the relative monad. -/
  η : ∀ {X}, toFunctor.obj X ⟶ T X
  /-- The multiplication for the monad. -/
  μ : ∀ {X Y}, ((toFunctor.obj X) ⟶ (T Y)) → ((T X) ⟶ (T Y))

  left_unit : ∀ {X}, μ (@η X) = 𝟙 _ := by aesop_cat

  right_unit : ∀ {X Y}, ∀ f : (toFunctor.obj X) ⟶ (T Y), η ≫ (μ f) = f := by aesop_cat

  assoc : ∀ {X Y Z}, ∀ f : (toFunctor.obj X) ⟶ (T Y), ∀ g : (toFunctor.obj Y) ⟶ (T Z),
    μ (f ≫ μ g) = (μ f) ≫ (μ g) := by aesop_cat

end CategoryTheory

universe u w v

/-- Type class for the relative pure operation -/
class RelativePure (r : Type u → Type w) (f : Type u → Type v) where
  /-- The relative pure operation -/
  pureᵣ : {α : Type u} → r α → f α

export RelativePure (pureᵣ)

/-- Type class for the relative bind operation -/
class RelativeBind (r : Type u → Type w) (m : Type u → Type v) where
  /-- The relative bind operation -/
  bindᵣ : {α β : Type u} → m α → (r α → m β) → m β

export RelativeBind (bindᵣ)

/-- Type class for the relative map operation -/
class RelativeFunctor (r : Type u → Type v) (f : Type u → Type w) where
  /-- The relative map operation -/
  mapᵣ : {α β : Type u} → (r α → r β) → (f α → f β)
  mapConstᵣ : {α β : Type u} → r α → f β → f α := mapᵣ ∘ Function.const _

export RelativeFunctor (mapᵣ mapConstᵣ)

-- Don't think sequencing makes sense in the relative setting?

-- class RelativeSeq (r : Type u → Type w) (m : Type u → Type v) [Seq r] where
--   /-- The relative seq operation -/
--   seqᵣ : {α β : Type u} → m (α → β) → (Unit → m α) → m β

-- export RelativeSeq (seqᵣ)

-- class RelativeSeqLeft (r : Type u → Type w) (m : Type u → Type v) where
--   /-- The relative seq left operation -/
--   seqLeftᵣ : {α β : Type u} → m α → (Unit → m β) → m α

-- export RelativeSeqLeft (seqLeftᵣ)

-- class RelativeSeqRight (r : Type u → Type w) (m : Type u → Type v) where
--   /-- The relative seq right operation -/
--   seqRightᵣ : {α β : Type u} → m α → (Unit → m β) → m β

-- export RelativeSeqRight (seqRightᵣ)

@[inherit_doc] infixl:55  " >>=ᵣ " => RelativeBind.bindᵣ
@[inherit_doc] infixr:100 " <$>ᵣ " => RelativeFunctor.mapᵣ
-- @[inherit_doc RelativeSeq.seqᵣ]           syntax:60 term:60 " <*>ᵣ " term:61 : term
-- @[inherit_doc RelativeSeqLeft.seqLeftᵣ]   syntax:60 term:60 " <*ᵣ " term:61 : term
-- @[inherit_doc RelativeSeqRight.seqRightᵣ] syntax:60 term:60 " *>ᵣ " term:61 : term

-- macro_rules | `($x <*>ᵣ $y) => `(RelativeSeq.seqᵣ $x fun _ : Unit => $y)
-- macro_rules | `($x <*ᵣ $y)  => `(RelativeSeqLeft.seqLeftᵣ $x fun _ : Unit => $y)
-- macro_rules | `($x *>ᵣ $y)  => `(RelativeSeqRight.seqRightᵣ $x fun _ : Unit => $y)

-- class RelativeApplicative (r : Type u → Type w) (m : Type u → Type v) [Seq r] [SeqLeft r] [SeqRight r] extends
--     RelativeFunctor r m, RelativePure r m, Seq m, SeqLeft m, SeqRight m where
--   map f x := Seq.seq (pureᵣ x) (fun _ => f)
--   seqLeft x y := Seq.seq (mapᵣ (fun y => ·) x) y
--   seqRight x y := Seq.seq (mapᵣ (fun y => y *> ·) x) y

/-- Type class for the relative monad -/
class RelativeMonad (r : Type u → Type w) (m : Type u → Type v) extends RelativePure r m, RelativeBind r m, RelativeFunctor r m where
  mapᵣ f x := bindᵣ x (pureᵣ ∘ f)

-- Cannot make this an instance due to synthesization order
def instSeqOfRelativeMonadOfSeq {r : Type u → Type w} {m : Type u → Type v}
    [RelativeMonad r m] [Seq r] : Seq m where
  seq f x := bindᵣ (r := r) (m := m) f (fun y => mapᵣ (y <*> ·) (x ()))

section Lawful

variable {r : Type u → Type w} {m f : Type u → Type v} {α β γ : Type u}

class LawfulRelativeFunctor (r : Type u → Type w) (f : Type u → Type v) [RelativeFunctor r f] where

  map_constᵣ {α β : Type u} : (mapConstᵣ : r α → f β → _) = mapᵣ ∘ (Function.const _)

  id_mapᵣ {α : Type u} (x : f α) : (id : r α → _) <$>ᵣ x = x

  comp_mapᵣ {α β γ : Type u} (g : r α → r β) (h : r β → r γ) (x : f α) :
    (h ∘ g) <$>ᵣ x = h <$>ᵣ g <$>ᵣ x

export LawfulRelativeFunctor (map_constᵣ id_mapᵣ comp_mapᵣ)

attribute [simp] id_mapᵣ

@[simp] theorem id_mapᵣ' [RelativeFunctor r f] [LawfulRelativeFunctor r f] (x : f α) :
    (fun a : r α => a) <$>ᵣ x = x :=
  id_mapᵣ x

@[simp] theorem RelativeFunctor.map_map [RelativeFunctor r f] [LawfulRelativeFunctor r f]
    (h : r α → r β) (g : r β → r γ) (x : f α) :
      g <$>ᵣ h <$>ᵣ x = (fun a => g (h a)) <$>ᵣ x :=
  (comp_mapᵣ _ _ _).symm

class LawfulRelativeMonad (r : Type u → Type w) (m : Type u → Type v) [RelativeMonad r m] extends
    LawfulRelativeFunctor r m where

  pure_bindᵣ {α β : Type u} (x : r α) (f : r α → m β) :
    (pureᵣ x) >>=ᵣ f = f x

  -- bind_mapᵣ : ∀ {α β : Type u} (f : m (α → β)) (x : m α),
  --   f >>=ᵣ (fun y => y <$>ᵣ x) =
  --     f <*> x

  bind_pure_compᵣ {α β : Type u} (f : r α → r β) (x : m α) :
    x >>=ᵣ (fun y => pureᵣ (f y)) = f <$>ᵣ x

  bind_assocᵣ {α β γ : Type u} (x : m α) (f : r α → m β) (g : r β → m γ) :
    x >>=ᵣ f >>=ᵣ g = x >>=ᵣ fun x ↦ f x >>=ᵣ g

export LawfulRelativeMonad (pure_bindᵣ bind_pure_compᵣ bind_assocᵣ)
attribute [simp] pure_bindᵣ bind_pure_compᵣ bind_assocᵣ

@[simp] theorem bind_pureᵣ [RelativeMonad r m] [LawfulRelativeMonad r m] (x : m α) :
    x >>=ᵣ pureᵣ (r := r) = x := by
  show x >>=ᵣ (fun a => pureᵣ (id a)) = x
  rw [bind_pure_compᵣ, id_mapᵣ]

end Lawful
