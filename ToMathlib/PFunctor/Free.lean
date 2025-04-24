/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.MonadHom
import ToMathlib.PFunctor.Basic
import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Data.PFunctor.Univariate.M
-- import Mathlib.CategoryTheory.Category.Basic
-- import Mathlib.CategoryTheory.InitialLimit

/-!
# Free Monad of a Polynomial Functor

We define the free monad on a **polynomial functor** (`PFunctor`), both as a separate inductive type `FreeM` (for programming) and as a `PFunctor` `Free` (for nice categorical properties), and prove some basic properties.

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

variable {P : PFunctor.{u}} {α β γ : Type v}

/-- Lift a position of the base polynomial functor into the free monad. -/
@[always_inline, inline]
def liftPos (a : P.A) : FreeM P (P.B a) := FreeM.roll a FreeM.pure

/-- Lift an object of the base polynomial functor into the free monad. -/
@[always_inline, inline]
def lift (x : P.Obj α) : FreeM P α := FreeM.roll x.1 (fun y ↦ FreeM.pure (x.2 y))

instance : MonadLift P (FreeM P) where
  monadLift x := FreeM.lift x

@[simp]
lemma monadLift_eq_lift (x : P.Obj α) : (x : FreeM P α) = FreeM.lift x := rfl

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

variable {m : Type u → Type v} {α : Type u}

/-- Canonical mapping of `FreeM P` into any other monad, given a map `s : (a : P.A) → m (P.B a)`. -/
protected def mapM [Pure m] [Bind m] (s : (a : P.A) → m (P.B a)) : FreeM P α → m α
  | .pure a => Pure.pure a
  | .roll a r => (s a) >>= (λ u ↦ (r u).mapM s)

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

-- Define the free monad as a PFunctor

#check WType

-- /-- The type of positions within a tree `w : W P`, representing a path from the root.
--     Defined recursively based on the structure of the tree `w`.
--     An element `Pos w` essentially selects a sequence of child indices down the tree.
--     This corresponds to the `B` component (fiber type) of the `Free P` pfunctor. -/
-- inductive Pos (P : PFunctor) : W P → Type _
--   /-- A position in a tree `WType.mk a f` is given by selecting a child `i : P.B a`
--       and specifying a position `tail` within that child's subtree `f i`. -/
--   | step {a : P.A} {f : P.B a → W P} (i : P.B a) (tail : Pos P (f i)) : Pos P (WType.mk a f)

-- inductive PosW (P : PFunctor) : W P → Type _
--   | root {a : P.A} {f : P.B a → W P} (r : P.A) : PosW P (WType.mk a f)
--   | next {a : P.A} {f : P.B a → W P} (i : P.B a) (tail : PosW P (f i)) : PosW P (WType.mk a f)

/-- Positions within the structure tree `(y + P).W` corresponding to the leaves (`y`-nodes).
    An element `FreePos P w` represents a path from the root of `w` to a leaf node
    that would hold a value of type `α` in `FreeM P α`. -/
inductive FreePos (P : PFunctor.{u}) : (1 + P).W → Type (max u v) where
  /-- The position corresponding to a leaf (`1`-node) in the structure tree. -/
  | here {f : PEmpty → (1 + P).W} : FreePos P (WType.mk (Sum.inl PUnit.unit) f)
  /-- A position within a child subtree `f i` of a `P` node. -/
  | there {a : P.A} {f : P.B a → (1 + P).W} (i : P.B a) (tail : FreePos P (f i)) : FreePos P (WType.mk (Sum.inr a) f)

-- What is the correct definition of `Free P`?
def Free (P : PFunctor) : PFunctor where
  A := (1 + P).W
  B := FreePos P -- Use the new FreePos definition

#check WType.equivSigma

#print WType.rec

/-- Map FreeM P α to Free P α (Sigma type representation). -/
@[simp]
def freeMToFree {P : PFunctor} {α : Type _} : FreeM P α → Free P α :=
  FreeM.construct
    (fun x => ⟨WType.mk (Sum.inl PUnit.unit) PEmpty.elim, fun _ => x⟩)
    (fun a _ ih =>
      let w_r (b : P.B a) : (1 + P).W := (ih b).1
      let g_r (b : P.B a) : FreePos P (w_r b) → α := (ih b).2
      ⟨WType.mk (Sum.inr a) w_r, fun p => match p with | FreePos.there b tail => g_r b tail⟩)

/-- Map Free P α (Sigma type representation) back to FreeM P α.

Need to uncurry in order for the compiler to recognize termination. -/
@[simp]
def freeToFreeMAux {P : PFunctor} {α : Type _} : (w : (1 + P).W) → (FreePos P w → α) → FreeM P α :=
  fun ⟨a, f⟩ g => match a with
    | Sum.inl PUnit.unit => FreeM.pure (g FreePos.here)
    | Sum.inr a => FreeM.roll a (fun b => freeToFreeMAux (f b) (fun tail => g (FreePos.there b tail)))

@[simp]
def freeToFreeM {P : PFunctor} {α : Type _} : Free P α → FreeM P α :=
  fun ⟨w, g⟩ => freeToFreeMAux w g

/-- One of the main results of this file: the free monad on a PFunctor is equivalent to the
    inductive type `FreeM`. -/
def equivFree {P : PFunctor} {α : Type _}: Free P α ≃ FreeM P α where
  toFun := freeToFreeM
  invFun := freeMToFree
  left_inv x := by -- requires proof by induction on (1 + P).W
    simp [Free] at x
    obtain ⟨a, g⟩ := x
    simp at a g
    rcases a with ⟨a | a, f⟩
    · simp [HAdd.hAdd, Add.add, coprod, OfNat.ofNat, One.one] at a f
      simp; congr
      · funext x; apply PEmpty.elim x
      · sorry
    · simp [HAdd.hAdd, Add.add, coprod, OfNat.ofNat, One.one] at f
      simp; congr
      · funext x; sorry
      · sorry

  right_inv x := by -- requires proof by induction on FreeM P α
    rcases x with a | ⟨a, r⟩
    · simp
    · simp; funext x
      unfold freeToFreeMAux
      split; rename_i c d e f g h h'
      rcases e with e | e
      · split
        · simp_all; sorry
        · contradiction
      · simp
        unfold FreeM.construct at h
        rcases hrx : (r x) with y | ⟨y, r'⟩
        · simp [hrx] at h ⊢
          have : Sum.inl PUnit.unit = Sum.inr e := (WType.mk.inj h).1
          simp at this
        · simp [hrx] at h ⊢
          have ⟨h1, h2⟩ := WType.mk.inj h
          have h1' : y = e := Sum.inr.inj h1
          simp [h1']
          rw [hrx] at h'
          simp at h'
          unfold freeToFreeMAux
          sorry


section Algebra

/-- An Algebra for a PFunctor `P` consists of a carrier type `X` and a structure map `P.Obj X → X`. -/
structure Algebra (P : PFunctor.{u}) where
  carrier : Type v
  toFun : P carrier → carrier

variable {P : PFunctor.{u}}

instance : CoeSort (Algebra P) (Type v) where
  coe alg := alg.carrier

instance : CoeFun (Algebra P) (fun alg => P alg.carrier → alg.carrier) where
  coe alg := alg.toFun

/-- A homomorphism between two Algebras `algA` and `algB` for the same PFunctor `P`
    is a function `f : algA.carrier → algB.carrier` that commutes with the structure maps. -/
structure AlgebraHom (P : PFunctor.{u}) (algA algB : Algebra P) where
  toFun : algA.carrier → algB.carrier
  commutes : ∀ (x : P algA.carrier), toFun (algA.toFun x) = algB.toFun (P.map toFun x)

variable {algA : Algebra P} {algB : Algebra P}

instance : CoeFun (AlgebraHom P algA algB) (fun _ => algA.carrier → algB.carrier) where
  coe hom := hom.toFun

@[ext]
theorem AlgebraHom.ext {f g : AlgebraHom P algA algB} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g; simp_all; exact funext h

/-- Identity homomorphism for an Algebra. -/
@[simps]
def AlgebraHom.id (P : PFunctor) (alg : Algebra P) : AlgebraHom P alg alg where
  toFun := fun x => x
  commutes _ := rfl

/-- Composition of Algebra homomorphisms. -/
@[simps]
def AlgebraHom.comp {algA algB algC : Algebra P} (f : AlgebraHom P algB algC) (g : AlgebraHom P algA algB) : AlgebraHom P algA algC where
  toFun := f.toFun ∘ g.toFun
  commutes x := by simp [f.commutes, g.commutes]

-- TODO: Define the Category instance for Algebra P

-- Show that `Free P` is an initial algebra for the category of Algebras P
-- State the universal property

def Algebra.initial (P : PFunctor) : Algebra P where
  carrier := (Free P).Idx
  toFun := sorry
  -- fun ⟨a, f⟩ => ⟨WType.mk a (fun b => (f b).1), PosW.root a⟩

-- def alpha {P : PFunctor} (alg : Algebra P) : (Algebra.initial P).carrier → alg.carrier :=
--   fun ⟨⟨a, f⟩, g⟩ => by
--     let toFunAlg : (a : P.A) × (P.B a → alg.carrier) → alg.carrier := alg.toFun
--     refine toFunAlg ⟨a, fun b => alpha alg ⟨f b, ?_⟩⟩
--     simp [Free] at g ⊢
--     obtain ⟨a', f'⟩ := f b
--     -- refine PosW.next ?_ ?_
--     rcases g with r | ⟨i, tail⟩
--     sorry

-- def AlgebraHom.initialMap {P : PFunctor} (alg : Algebra P) : AlgebraHom P (Algebra.initial P) alg where
--   toFun := alpha alg
--   commutes := sorry

end Algebra

section Coalgebra

/-- A Coalgebra for a PFunctor `P` consists of a carrier type `X` and a structure map `X → P.Obj X`. -/
structure Coalgebra (P : PFunctor.{u}) where
  carrier : Type v
  toFun : carrier → P carrier

variable {P : PFunctor.{u}}

instance : CoeSort (Coalgebra P) (Type v) where
  coe coalg := coalg.carrier

instance : CoeFun (Coalgebra P) (fun coalg => coalg.carrier → P coalg.carrier) where
  coe coalg := coalg.toFun

/-- A homomorphism between two Coalgebras `coalgA` and `coalgB` for the same PFunctor `P`
    is a function `f : coalgA.carrier → coalgB.carrier` that commutes with the structure maps. -/
structure CoalgebraHom (P : PFunctor.{u}) (coalgA coalgB : Coalgebra P) where
  toFun : coalgA.carrier → coalgB.carrier
  commutes : ∀ (x : coalgA.carrier), coalgB.toFun (toFun x) = P.map toFun (coalgA.toFun x)

variable {coalgA : Coalgebra P} {coalgB : Coalgebra P}

instance : CoeFun (CoalgebraHom P coalgA coalgB) (fun _ => coalgA.carrier → coalgB.carrier) where
  coe hom := hom.toFun

@[ext]
theorem CoalgebraHom.ext {f g : CoalgebraHom P coalgA coalgB} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g; simp_all; exact funext h

/-- Identity homomorphism for a Coalgebra. -/
@[simps]
def CoalgebraHom.id (P : PFunctor) (coalg : Coalgebra P) : CoalgebraHom P coalg coalg where
  toFun := fun x => x
  commutes _ := rfl

/-- Composition of Coalgebra homomorphisms. -/
@[simps]
def CoalgebraHom.comp {coalgA coalgB coalgC : Coalgebra P} (f : CoalgebraHom P coalgB coalgC) (g : CoalgebraHom P coalgA coalgB) : CoalgebraHom P coalgA coalgC where
  toFun := f.toFun ∘ g.toFun
  commutes x := by simp [f.commutes, g.commutes]

-- TODO: Define the Category instance for Coalgebra P

end Coalgebra

-- TODO: how is the free monad itself a PFunctor?

end PFunctor
