/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.PFunctor.Multivariate.Basic

/-!
  # Polynomial Functors, Lens, and Charts

  This file defines polynomial functors, lenses, and charts. The goal is to provide basic
  definitions, with their properties and categories defined in later files.
-/

universe u v

namespace PFunctor

/-- Lift a polynomial functor to a larger universe. -/
protected def ulift (P : PFunctor.{u}) : PFunctor.{max u v} :=
  ⟨ULift P.A, fun a => ULift (P.B (ULift.down a))⟩

/-- The zero polynomial functor -/
def zero : PFunctor.{u} := ⟨PEmpty, fun _ => PEmpty⟩

/-- The unit polynomial functor -/
def one : PFunctor.{u} := ⟨PUnit, fun _ => PEmpty⟩

instance : Zero PFunctor.{u} where
  zero := zero

instance : One PFunctor.{u} where
  one := one

/-- The variable `y` polynomial functor. This is the unit for composition. -/
def y : PFunctor.{u} :=
  ⟨PUnit, fun _ => PUnit⟩

instance : IsEmpty zero.A := inferInstanceAs (IsEmpty PEmpty)
instance : IsEmpty (A 0) := inferInstanceAs (IsEmpty PEmpty)
instance : Unique one.A := inferInstanceAs (Unique PUnit)
instance : Unique (A 1) := inferInstanceAs (Unique PUnit)
instance : Unique y.A := inferInstanceAs (Unique PUnit)

/-- The monomial functor `P(y) = A y^B` -/
def monomial (A B : Type u) : PFunctor.{u} :=
  ⟨A, fun _ => B⟩

@[inherit_doc] infixr:80 " y^" => monomial

/-- The constant functor `P(y) = A` -/
def C (A : Type u) : PFunctor.{u} :=
  A y^ PEmpty

/-- The linear functor `P(y) = A y` -/
def linear (A : Type u) : PFunctor.{u} :=
  A y^ PUnit

/-- The self monomial functor `P(y) = S y^S` -/
def selfMonomial (S : Type u) : PFunctor.{u} := S y^S

/-- The pure power functor `P(y) = y^B` -/
def purePower (B : Type u) : PFunctor.{u} :=
  PUnit y^ B

/-- A polynomial functor is representable if it is equivalent to `y^A` for some type `A`. -/
alias representable := purePower

section Coprod

/-- Coprod (sum) of polynomial functors `P + Q` -/
def coprod (P Q : PFunctor.{u}) : PFunctor.{u} :=
  ⟨P.A ⊕ Q.A, Sum.elim P.B Q.B⟩

instance : Add PFunctor.{u} where
  add := coprod

alias coprodUnit := zero

/-- Generalized coproduct (sigma type) of an indexed family of polynomial functors -/
def sigma {I : Type v} (F : I → PFunctor.{u}) : PFunctor.{max u v} :=
  ⟨Σ i, (F i).A, fun ⟨i, a⟩ => ULift ((F i).B a)⟩

-- macro "Σₚ" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``sigma xs b

end Coprod

section Prod

/-- Product of polynomial functors `P * Q` -/
def prod (P Q : PFunctor.{u}) : PFunctor.{u} :=
  ⟨P.A × Q.A, fun ab => P.B ab.1 ⊕ Q.B ab.2⟩

instance : Mul PFunctor.{u} where
  mul := prod

alias prodUnit := one

/-- Generalized product (pi type) of an indexed family of polynomial functors -/
def pi {I : Type v} (F : I → PFunctor.{u}) : PFunctor.{max u v} :=
  ⟨(i : I) → (F i).A, fun f => Σ i, (F i).B (f i)⟩

end Prod

section Comp

/-- Infix notation for `PFunctor.comp P Q` -/
infixl:80 " ◂ " => PFunctor.comp

/-- The unit for composition `Y` -/
alias compUnit := y

/-- Repeated composition `P ◂ P ◂ ... ◂ P` (n times). -/
@[simp]
def compNth (P : PFunctor.{u}) : Nat → PFunctor.{u}
  | 0 => y
  | Nat.succ n => P ◂ compNth P n

instance : NatPow PFunctor.{u} where
  pow := compNth

end Comp

/-- Exponential of polynomial functors `P ^ Q` -/
def exp (P Q : PFunctor.{u}) : PFunctor.{u} :=
  pi (fun a => P ◂ (y + C (Q.B a)))

instance : Pow PFunctor.{u} PFunctor.{u} where
  pow := exp

section Tensor

/-- Tensor or parallel product of polynomial functors -/
def tensor (P Q : PFunctor.{u}) : PFunctor.{u} :=
  ⟨P.A × Q.A, fun ab => P.B ab.1 × Q.B ab.2⟩

/-- Infix notation for tensor product `P ⊗ₚ Q` -/
infixl:70 " ⊗ₚ " => tensor

/-- The unit for the tensor product `Y` -/
alias tensorUnit := y

end Tensor

section Fintype

/-- A polynomial functor is finitely branching if each of its branches is a finite type. -/
protected class Fintype (P : PFunctor.{u}) where
  fintype_B : ∀ a, Fintype (P.B a)

instance {P : PFunctor.{u}} [inst : P.Fintype] : PFunctor.Fintype (PFunctor.ulift P) where
  fintype_B := fun a => by
    unfold PFunctor.ulift
    haveI : Fintype (P.B (ULift.down a)) := inst.fintype_B (ULift.down a)
    infer_instance

@[simp]
instance {P : PFunctor.{u}} [inst : P.Fintype] : ∀ a, Fintype (P.B a) := fun a => inst.fintype_B a

end Fintype





/-- A **lens** between two polynomial functors `P` and `Q` is a pair of a function:
- `mapPos : P.A → Q.A`
- `mapDir : ∀ a, Q.B (mapPos a) → P.B a` -/
structure Lens (P Q : PFunctor.{u}) where
  mapPos : P.A → Q.A
  mapDir : ∀ a, Q.B (mapPos a) → P.B a

/-- Infix notation for constructing a lens `mapPos ⇆ mapDir` -/
infixr:25 " ⇆ " => Lens.mk

namespace Lens

/-- The identity lens -/
protected def id (P : PFunctor.{u}) : Lens P P where
  mapPos := _root_.id
  mapDir := fun _ b => b

/-- Composition of lenses -/
def comp {P Q R : PFunctor.{u}} (l : Lens Q R) (l' : Lens P Q) : Lens P R where
  mapPos := l.mapPos ∘ l'.mapPos
  mapDir := fun i => (l'.mapDir i) ∘ l.mapDir (l'.mapPos i)

@[inherit_doc] infixl:75 " ∘ₗ " => comp

@[simp]
theorem id_comp {P Q : PFunctor.{u}} (f : Lens P Q) : (Lens.id Q) ∘ₗ f = f := rfl

@[simp]
theorem comp_id {P Q : PFunctor.{u}} (f : Lens P Q) : f ∘ₗ (Lens.id P) = f := rfl

theorem comp_assoc {P Q R S : PFunctor.{u}} (l : Lens R S) (l' : Lens Q R) (l'' : Lens P Q) :
    (l ∘ₗ l') ∘ₗ l'' = l ∘ₗ (l' ∘ₗ l'') := rfl

/-- An equivalence between two polynomial functors `P` and `Q`, using lenses.
    This corresponds to an isomorphism in the category `PFunctor` with `Lens` morphisms. -/
@[ext]
structure Equiv (P Q : PFunctor.{u}) where
  toLens : Lens P Q
  invLens : Lens Q P
  left_inv : comp invLens toLens = Lens.id P
  right_inv : comp toLens invLens = Lens.id Q

@[inherit_doc] infix:50 " ≃ₗ " => Equiv

namespace Equiv

@[refl]
def refl (P : PFunctor.{u}) : P ≃ₗ P :=
  ⟨Lens.id P, Lens.id P, rfl, rfl⟩

@[symm]
def symm {P Q : PFunctor.{u}} (e : P ≃ₗ Q) : Q ≃ₗ P :=
  ⟨e.invLens, e.toLens, e.right_inv, e.left_inv⟩

@[trans]
def trans {P Q R : PFunctor.{u}} (e₁ : P ≃ₗ Q) (e₂ : Q ≃ₗ R) : P ≃ₗ R :=
  ⟨e₂.toLens ∘ₗ e₁.toLens, e₁.invLens ∘ₗ e₂.invLens,
    by
      rw [comp_assoc]
      rw (occs := [2]) [← comp_assoc]
      simp [e₁.left_inv, e₂.left_inv],
    by
      rw [comp_assoc]
      rw (occs := [2]) [← comp_assoc]
      simp [e₁.right_inv, e₂.right_inv]⟩

end Equiv

/-- The (unique) initial lens from the zero functor to any functor `P`. -/
def initial {P : PFunctor.{u}} : Lens 0 P :=
  PEmpty.elim ⇆ fun a => PEmpty.elim a

/-- The (unique) terminal lens from any functor `P` to the unit functor `1`. -/
def terminal {P : PFunctor.{u}} : Lens P 1 :=
  (fun _ => PUnit.unit) ⇆ (fun _ => PEmpty.elim)

alias fromZero := initial
alias toOne := terminal

/-- Left injection lens `inl : P → P + Q` -/
def inl {P Q : PFunctor.{u}} : Lens P (P + Q) :=
  Sum.inl ⇆ (fun _ d => d)

/-- Right injection lens `inr : Q → P + Q` -/
def inr {P Q : PFunctor.{u}} : Lens Q (P + Q) :=
  Sum.inr ⇆ (fun _ d => d)

/-- Copairing of lenses `[l₁, l₂]ₗ : P + Q → R` -/
def coprodPair {P Q R : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q R) : Lens (P + Q) R :=
  (Sum.elim l₁.mapPos l₂.mapPos) ⇆
    (fun a d => match a with
      | Sum.inl pa => l₁.mapDir pa d
      | Sum.inr qa => l₂.mapDir qa d)

/-- Parallel application of lenses for coproduct `l₁ ⊎ l₂ : P + Q → R + W` -/
def coprodMap {P Q R W : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q W) : Lens (P + Q) (R + W) :=
  (Sum.map l₁.mapPos l₂.mapPos) ⇆
    (fun psum => match psum with
      | Sum.inl pa => l₁.mapDir pa
      | Sum.inr qa => l₂.mapDir qa)


-- def sigmaExists
-- def sigmaMap

/-- Projection lens `fst : P * Q → P` -/
def fst {P Q : PFunctor.{u}} : Lens (P * Q) P :=
  Prod.fst ⇆ (fun _ => Sum.inl)

/-- Projection lens `snd : P * Q → Q` -/
def snd {P Q : PFunctor.{u}} : Lens (P * Q) Q :=
  Prod.snd ⇆ (fun _ => Sum.inr)

/-- Pairing of lenses `⟨l₁, l₂⟩ₗ : P → Q * R` -/
def prodPair {P Q R : PFunctor.{u}} (l₁ : Lens P Q) (l₂ : Lens P R) : Lens P (Q * R) :=
  (fun p => (l₁.mapPos p, l₂.mapPos p)) ⇆
    (fun p => Sum.elim (l₁.mapDir p) (l₂.mapDir p))

/-- Parallel application of lenses for product `l₁ ×ₗ l₂ : P * Q → R * W` -/
def prodMap {P Q R W : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q W) : Lens (P * Q) (R * W) :=
  (fun pq => (l₁.mapPos pq.1, l₂.mapPos pq.2)) ⇆
    (fun pq => Sum.elim (Sum.inl ∘ l₁.mapDir pq.1) (Sum.inr ∘ l₂.mapDir pq.2))

-- def piForall
-- def piMap

/-- Apply lenses to both sides of a composition: `l₁ ◂ₗ l₂ : (P ◂ Q ⇆ R ◂ W)` -/
def compMap {P Q R W : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q W) : Lens (P ◂ Q) (R ◂ W) :=
  (fun ⟨pa, pq⟩ => ⟨l₁.mapPos pa, fun rb' => l₂.mapPos (pq (l₁.mapDir pa rb'))⟩) ⇆
    (fun ⟨pa, pq⟩ ⟨rb, wc⟩ =>
      let pb := l₁.mapDir pa rb
      let qc := l₂.mapDir (pq pb) wc
      ⟨pb, qc⟩)

/-- Apply lenses to both sides of a tensor / parallel product: `l₁ ⊗ₗ l₂ : (P ⊗ₚ Q ⇆ R ⊗ₚ W)` -/
def tensorMap {P Q R W : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q W) : Lens (P ⊗ₚ Q) (R ⊗ₚ W) :=
  (fun ⟨pa, qa⟩ => (l₁.mapPos pa, l₂.mapPos qa)) ⇆
    (fun ⟨_pa, qa⟩ ⟨rb, wb⟩ => (l₁.mapDir _pa rb, l₂.mapDir qa wb))

/-- Lens to introduce `y` on the right: `P → P ◂ y` -/
def tildeR {P : PFunctor.{u}} : Lens P (P ◂ y) :=
  (fun a => ⟨a, fun _ => PUnit.unit⟩) ⇆ (fun _a => fun ⟨b, _⟩ => b)

/-- Lens to introduce `y` on the left: `P → y ◂ P` -/
def tildeL {P : PFunctor.{u}} : Lens P (y ◂ P) :=
  (fun a => ⟨PUnit.unit, fun _ => a⟩) ⇆ (fun _a => fun ⟨_, b⟩ => b)

/-- Lens from `P ◂ y` to `P` -/
def invTildeR {P : PFunctor.{u}} : Lens (P ◂ y) P :=
  (fun a => a.1) ⇆ (fun _ b => ⟨b, PUnit.unit⟩)

/-- Lens from `y ◂ P` to `P` -/
def invTildeL {P : PFunctor.{u}} : Lens (y ◂ P) P :=
  (fun ⟨_, f⟩ => f PUnit.unit) ⇆ (fun _ b => ⟨PUnit.unit, b⟩)

@[inherit_doc] infixl:75 " ◂ₗ " => compMap
@[inherit_doc] infixl:75 " ×ₗ " => prodMap
@[inherit_doc] infixl:75 " ⊎ₗ " => coprodMap
@[inherit_doc] infixl:75 " ⊗ₗ " => tensorMap
notation "[" l₁ "," l₂ "]ₗ" => coprodPair l₁ l₂
notation "⟨" l₁ "," l₂ "⟩ₗ" => prodPair l₁ l₂

/-- The type of lenses from a polynomial functor `P` to `y` -/
def enclose (P : PFunctor.{u}) : Type u :=
  Lens P y

/-- Helper lens for `speedup` -/
def fixState {S : Type u} : Lens (selfMonomial S) (selfMonomial S ◂ selfMonomial S) :=
  (fun s₀ => ⟨s₀, fun s₁ => s₁⟩) ⇆ (fun _s₀ => fun ⟨_s₁, s₂⟩ => s₂)

/-- The `speedup` lens operation: `Lens (S y^S) P → Lens (S y^S) (P ◂ P)` -/
def speedup {S : Type u} {P : PFunctor.{u}} (l : Lens (selfMonomial S) P) :
    Lens (selfMonomial S) (P ◂ P) :=
  (l ◂ₗ l) ∘ₗ fixState

end Lens

/-- A chart between two polynomial functors `P` and `Q` is a pair of a function:
- `mapPos : P.A → Q.A`
- `mapDir : ∀ a, P.B a → Q.B (mapPos a)` -/
structure Chart (P Q : PFunctor.{u}) where
  mapPos : P.A → Q.A
  mapDir : ∀ a, P.B a → Q.B (mapPos a)

/-- Infix notation for constructing a chart `mapPos ⇉ mapDir` -/
infixr:25 " ⇉ " => Chart.mk

namespace Chart

/-- The identity chart -/
protected def id (P : PFunctor.{u}) : Chart P P := id ⇉ fun _ => id

/-- Composition of charts -/
def comp {P Q R : PFunctor.{u}} (c' : Chart Q R) (c : Chart P Q) : Chart P R where
  mapPos := c'.mapPos ∘ c.mapPos
  mapDir := fun i => c'.mapDir (c.mapPos i) ∘ c.mapDir i

/-- Infix notation for chart composition `c' ∘c c` -/
infixl:75 " ∘c " => comp

@[simp]
theorem id_comp {P Q : PFunctor.{u}} (f : Chart P Q) : (Chart.id Q) ∘c f = f := rfl

@[simp]
theorem comp_id {P Q : PFunctor.{u}} (f : Chart P Q) : f ∘c (Chart.id P) = f := rfl

theorem comp_assoc {P Q R S : PFunctor.{u}} (c : Chart R S) (c' : Chart Q R) (c'' : Chart P Q) :
    (c ∘c c') ∘c c'' = c ∘c (c' ∘c c'') := rfl

/-- An equivalence between two polynomial functors `P` and `Q`, using charts.
    This corresponds to an isomorphism in the category `PFunctor` with `Chart` morphisms. -/
@[ext]
structure Equiv (P Q : PFunctor.{u}) where
  toChart : Chart P Q
  invChart : Chart Q P
  left_inv : comp invChart toChart = Chart.id P
  right_inv : comp toChart invChart = Chart.id Q

/-- Infix notation for chart equivalence `P ≃c Q` -/
infix:50 " ≃c " => Equiv

namespace Equiv

@[refl]
def refl (P : PFunctor.{u}) : P ≃c P :=
  ⟨Chart.id P, Chart.id P, rfl, rfl⟩

@[symm]
def symm {P Q : PFunctor.{u}} (e : P ≃c Q) : Q ≃c P :=
  ⟨e.invChart, e.toChart, e.right_inv, e.left_inv⟩

def trans {P Q R : PFunctor.{u}} (e₁ : P ≃c Q) (e₂ : Q ≃c R) : P ≃c R :=
  ⟨e₂.toChart ∘c e₁.toChart, e₁.invChart ∘c e₂.invChart,
    by
      rw [comp_assoc]
      rw (occs := [2]) [← comp_assoc]
      simp [e₁.left_inv, e₂.left_inv],
    by
      rw [comp_assoc]
      rw (occs := [2]) [← comp_assoc]
      simp [e₁.right_inv, e₂.right_inv]⟩

end Equiv

/-- The (unique) initial chart from the zero functor to any functor `P`. -/
def initial {P : PFunctor.{u}} : Chart 0 P :=
  PEmpty.elim ⇉ fun _ => PEmpty.elim

/-- The (unique) terminal chart from any functor `P` to the functor `Y`. -/
def terminal {P : PFunctor.{u}} : Chart P y :=
  (fun _ => PUnit.unit) ⇉ (fun _ _ => PUnit.unit)

alias fromZero := initial
alias toOne := terminal

end Chart

section Lemmas

@[ext (iff := false)]
theorem ext {P Q : PFunctor.{u}} (h : P.A = Q.A) (h' : ∀ a, P.B a = Q.B (h ▸ a)) : P = Q := by
  cases P; cases Q; simp at h h' ⊢; subst h; simp_all; funext; exact h' _

@[ext (iff := false)]
theorem Lens.ext {P Q : PFunctor.{u}} (l₁ l₂ : Lens P Q)
    (h₁ : ∀ a, l₁.mapPos a = l₂.mapPos a) (h₂ : ∀ a, l₁.mapDir a = (h₁ a) ▸ l₂.mapDir a) :
    l₁ = l₂ := by
  rcases l₁ with ⟨mapPos₁, _⟩
  rcases l₂ with ⟨mapPos₂, _⟩
  have h : mapPos₁ = mapPos₂ := funext h₁
  subst h
  simp_all
  exact funext h₂

@[ext (iff := false)]
theorem Chart.ext {P Q : PFunctor.{u}} (c₁ c₂ : Chart P Q)
    (h₁ : ∀ a, c₁.mapPos a = c₂.mapPos a) (h₂ : ∀ a, c₁.mapDir a = (h₁ a) ▸ c₂.mapDir a) :
    c₁ = c₂ := by
  rcases c₁ with ⟨mapPos₁, _⟩
  rcases c₂ with ⟨mapPos₂, _⟩
  have h : mapPos₁ = mapPos₂ := funext h₁
  subst h
  simp_all
  exact funext h₂

@[simp] theorem C_zero : C PEmpty = 0 := rfl
@[simp] theorem C_one : C PUnit = 1 := rfl

@[simp] lemma zero_A : zero.A = PEmpty := rfl
@[simp] lemma zero_B (a : zero.A) : zero.B a = PEmpty := PEmpty.elim a

@[simp] lemma one_A : one.A = PUnit := rfl
@[simp] lemma one_B (a : one.A) : one.B a = PEmpty := rfl

@[simp] lemma y_A : y.A = PUnit := rfl
@[simp] lemma y_B (a : y.A) : y.B a = PUnit := rfl

@[simp] lemma C_A (A : Type u) : (C A).A = A := rfl
@[simp] lemma C_B (A : Type u) (a : (C A).A) : (C A).B a = PEmpty := rfl

@[simp] lemma linear_A (A : Type u) : (linear A).A = A := rfl
@[simp] lemma linear_B (A : Type u) (a : (linear A).A) : (linear A).B a = PUnit := rfl

@[simp] lemma purePower_A (B : Type u) : (purePower B).A = PUnit := rfl
@[simp] lemma purePower_B (B : Type u) (a : (purePower B).A) : (purePower B).B a = B := rfl

lemma y_eq_linear_pUnit : y = linear PUnit := rfl
lemma y_eq_purePower_pUnit : y = purePower PUnit := rfl

section ULift

variable {P : PFunctor.{u}}

@[simp]
theorem ulift_A : (P.ulift).A = ULift P.A := rfl

@[simp]
theorem ulift_B {a : P.A} : (P.ulift).B (ULift.up a) = ULift (P.B a) := rfl

namespace Lens.Equiv

def ulift : P.ulift ≃ₗ P where
  toLens := (fun a => ULift.down a) ⇆ (fun _ b => ULift.up b)
  invLens := (fun a => ULift.up a) ⇆ (fun _ b => ULift.down b)
  left_inv := rfl
  right_inv := rfl

end Lens.Equiv

end ULift

namespace Lens

section Coprod

@[simp]
theorem coprodMap_comp_inl {P Q R W : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    ((l₁ ⊎ₗ l₂) ∘ₗ Lens.inl) = (Lens.inl ∘ₗ l₁) := rfl

@[simp]
theorem coprodMap_comp_inr {P Q R W : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    (l₁ ⊎ₗ l₂) ∘ₗ Lens.inr = Lens.inr ∘ₗ l₂ := rfl

theorem coprodPair_comp_coprodMap {P Q R W X : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q W)
    (f : Lens R X) (g : Lens W X) :
  Lens.coprodPair f g ∘ₗ (l₁ ⊎ₗ l₂) = Lens.coprodPair (f ∘ₗ l₁) (g ∘ₗ l₂) := by
  ext a <;> rcases a with a | a <;> rfl

@[simp]
theorem coprodPair_comp_inl {P Q R : PFunctor.{u}} (f : Lens P R) (g : Lens Q R) :
    Lens.coprodPair f g ∘ₗ Lens.inl = f := rfl

@[simp]
theorem coprodPair_comp_inr {P Q R : PFunctor.{u}} (f : Lens P R) (g : Lens Q R) :
    Lens.coprodPair f g ∘ₗ Lens.inr = g := rfl

theorem comp_inl_inr {P Q R : PFunctor.{u}} (h : Lens (P + Q) R) :
    Lens.coprodPair (h ∘ₗ Lens.inl) (h ∘ₗ Lens.inr) = h := by
  ext a <;> rcases a <;> rfl

@[simp]
theorem coprodMap_id {P Q : PFunctor.{u}} :
    Lens.coprodMap (Lens.id P) (Lens.id Q) = Lens.id (P + Q) := by
  ext a <;> rcases a <;> rfl

@[simp]
theorem coprodPair_inl_inr {P Q : PFunctor.{u}} :
    Lens.coprodPair Lens.inl Lens.inr = Lens.id (P + Q) := by
  ext a <;> rcases a <;> rfl

namespace Equiv

/-- Commutativity of coproduct -/
def coprodComm (P Q : PFunctor.{u}) : P + Q ≃ₗ Q + P where
  toLens := Lens.coprodPair Lens.inr Lens.inl
  invLens := Lens.coprodPair Lens.inr Lens.inl
  left_inv := by
    ext a <;> rcases a with a | a <;> rfl
  right_inv := by
    ext a <;> rcases a with a | a <;> rfl

@[simp]
theorem coprodComm_symm {P Q : PFunctor.{u}} : (coprodComm P Q).symm = coprodComm Q P := rfl

/-- Associativity of coproduct -/
def coprodAssoc {P Q R : PFunctor.{u}} : (P + Q) + R ≃ₗ P + (Q + R) where
  toLens := -- Maps (P + Q) + R to P + (Q + R)
    Lens.coprodPair
      (Lens.coprodPair -- Maps P + Q to P + (Q + R)
        (Lens.inl) -- Maps P to P + (Q + R) via Sum.inl
        (Lens.inr ∘ₗ Lens.inl) -- Maps Q to P + (Q + R) via Sum.inr ∘ Sum.inl
      )
      (Lens.inr ∘ₗ Lens.inr) -- Maps R to P + (Q + R) via Sum.inr ∘ Sum.inr
  invLens := -- Maps P + (Q + R) to (P + Q) + R
    Lens.coprodPair
      (Lens.inl ∘ₗ Lens.inl) -- Maps P to (P + Q) + R via Sum.inl ∘ Sum.inl
      (Lens.coprodPair -- Maps Q + R to (P + Q) + R
        (Lens.inl ∘ₗ Lens.inr) -- Maps Q to (P + Q) + R via Sum.inl ∘ Sum.inr
        (Lens.inr) -- Maps R to (P + Q) + R via Sum.inr
      )
  left_inv := by
    ext a <;> rcases a with (a | a) |a <;> rfl
  right_inv := by
    ext a <;> rcases a with a | a |a <;> rfl

/-- Coproduct with `0` is identity (right) -/
def coprodZero {P : PFunctor.{u}} : P + 0 ≃ₗ P where
  toLens := Lens.coprodPair (Lens.id P) Lens.initial
  invLens := Lens.inl
  left_inv := by
    ext a <;> rcases a with a | a
    · rfl
    · exact PEmpty.elim a
    · rfl
    · exact PEmpty.elim a
  right_inv := by
    ext <;> rfl

/-- Coproduct with `0` is identity (left) -/
def zeroCoprod {P : PFunctor.{u}} : 0 + P ≃ₗ P where
  toLens := Lens.coprodPair Lens.initial (Lens.id P)
  invLens := Lens.inr
  left_inv := by
    ext a <;> rcases a with a | a
    · exact PEmpty.elim a
    · rfl
    · exact PEmpty.elim a
    · rfl
  right_inv := by
    ext <;> rfl

end Equiv

end Coprod

section Prod

@[simp]
theorem fst_comp_prodMap {P Q R W : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.fst ∘ₗ (l₁ ×ₗ l₂) = l₁ ∘ₗ Lens.fst := rfl

@[simp]
theorem snd_comp_prodMap {P Q R W : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.snd ∘ₗ (l₁ ×ₗ l₂) = l₂ ∘ₗ Lens.snd := rfl

theorem prodMap_comp_prodPair {P Q R W X : PFunctor.{u}} (l₁ : Lens Q W) (l₂ : Lens R X)
  (f : Lens P Q) (g : Lens P R) :
    (l₁ ×ₗ l₂) ∘ₗ Lens.prodPair f g = Lens.prodPair (l₁ ∘ₗ f) (l₂ ∘ₗ g) := by
  ext a x
  · rfl
  · cases x <;> rfl

@[simp]
theorem fst_comp_prodPair {P Q R : PFunctor.{u}} (f : Lens P Q) (g : Lens P R) :
    Lens.fst ∘ₗ Lens.prodPair f g = f := rfl

@[simp]
theorem snd_comp_prodPair {P Q R : PFunctor.{u}} (f : Lens P Q) (g : Lens P R) :
    Lens.snd ∘ₗ Lens.prodPair f g = g := rfl

theorem comp_fst_snd {P Q R : PFunctor.{u}} (h : Lens P (Q * R)) :
    Lens.prodPair (Lens.fst ∘ₗ h) (Lens.snd ∘ₗ h) = h := by
  ext a x
  · rfl
  · cases x <;> rfl

@[simp]
theorem prodMap_id {P Q : PFunctor.{u}} :
    Lens.prodMap (Lens.id P) (Lens.id Q) = Lens.id (P * Q) := by
  ext a x
  · rfl
  · cases x <;> rfl

@[simp]
theorem prodPair_fst_snd {P Q : PFunctor.{u}} :
    Lens.prodPair Lens.fst Lens.snd = Lens.id (P * Q) := by
  ext a x
  · rfl
  · cases x <;> rfl

namespace Equiv

/-- Commutativity of product -/
def prodComm (P Q : PFunctor.{u}) : P * Q ≃ₗ Q * P where
  toLens := Prod.swap ⇆ (fun _ => Sum.elim Sum.inr Sum.inl)
  invLens := Prod.swap ⇆ (fun _ => Sum.elim Sum.inr Sum.inl)
  left_inv := by
    ext _ b
    · rfl
    · cases b <;> rfl
  right_inv := by
    ext _ b
    · rfl
    · cases b <;> rfl

@[simp]
theorem prodComm_symm {P Q : PFunctor.{u}} : (prodComm P Q).symm = prodComm Q P := rfl

/-- Associativity of product -/
def prodAssoc {P Q R : PFunctor.{u}} : (P * Q) * R ≃ₗ P * (Q * R) where
  toLens := (_root_.Equiv.prodAssoc P.A Q.A R.A).toFun ⇆
              (fun _ d => (Equiv.sumAssoc _ _ _).invFun d)
  invLens := (_root_.Equiv.prodAssoc P.A Q.A R.A).invFun ⇆
               (fun _ d => Equiv.sumAssoc _ _ _ d)
  left_inv := by
    ext _ b
    · rfl
    · rcases b with b | _
      · cases b <;> rfl
      · rfl
  right_inv := by
    ext _ b
    · rfl
    · rcases b with _ | b
      · rfl
      · cases b <;> rfl

/-- Product with `1` is identity (right) -/
def prodOne {P : PFunctor.{u}} : P * 1 ≃ₗ P where
  toLens := Prod.fst ⇆ (fun _ => Sum.inl)
  invLens := (fun p => (p, PUnit.unit)) ⇆ (fun _ => Sum.elim id PEmpty.elim)
  left_inv := by
    ext _ b
    · rfl
    · rcases b with _ | b
      · rfl
      · cases b
  right_inv := by
    ext <;> rfl

/-- Product with `1` is identity (left) -/
def oneProd {P : PFunctor.{u}} : 1 * P ≃ₗ P where
  toLens := Prod.snd ⇆ (fun _ => Sum.inr)
  invLens := (fun p => (PUnit.unit, p)) ⇆ (fun _ => Sum.elim PEmpty.elim id)
  left_inv := by
    ext _ b
    · rfl
    · rcases b with b | _
      · cases b
      · rfl
  right_inv := by
    ext <;> rfl

/-- Product with `0` is zero (right) -/
def prodZero {P : PFunctor.{u}} : P * 0 ≃ₗ 0 where
  toLens := (fun a => PEmpty.elim a.2) ⇆ (fun _ x => PEmpty.elim x)
  invLens := PEmpty.elim ⇆ (fun pe _ => PEmpty.elim pe)
  left_inv := by
    ext ⟨_, a⟩ _ <;> exact PEmpty.elim a
  right_inv := by
    ext ⟨_, _⟩

/-- Product with `0` is zero (left) -/
def zeroProd {P : PFunctor.{u}} : 0 * P ≃ₗ 0 where
  toLens := (fun ⟨pa, _⟩ => PEmpty.elim pa) ⇆ (fun _ x => PEmpty.elim x)
  invLens := PEmpty.elim ⇆ (fun pe _ => PEmpty.elim pe)
  left_inv := by
    ext ⟨a, _⟩ <;> exact PEmpty.elim a
  right_inv := by
    ext ⟨_, _⟩

/-- Left distributive law for product over coproduct -/
def prodCoprodDistrib {P Q R : PFunctor.{u}} : P * (Q + R) ≃ₗ (P * Q) + (P * R) where
  toLens := (fun ⟨p, qr⟩ => match qr with
              | Sum.inl q => Sum.inl (p, q)
              | Sum.inr r => Sum.inr (p, r)) ⇆
            (fun ⟨_, qr⟩ => match qr with
              | Sum.inl _ => id -- P.B p ⊕ Q.B q
              | Sum.inr _ => id) -- P.B p ⊕ R.B r
  invLens := (Sum.elim
              (fun ⟨p, q⟩ => (p, Sum.inl q))
              (fun ⟨p, r⟩ => (p, Sum.inr r))) ⇆
             (fun pq_pr => match pq_pr with
              | Sum.inl _ => id -- P.B p ⊕ Q.B q
              | Sum.inr _ => id) -- P.B p ⊕ R.B r
  left_inv := by
    ext a <;> rcases a with ⟨p, q | r⟩ <;> rfl
  right_inv := by
    ext a <;> rcases a with ⟨p, q⟩ | ⟨p, r⟩ <;> rfl

/-- Right distributive law for coproduct over product -/
def coprodProdDistrib {P Q R : PFunctor.{u}} : (Q + R) * P ≃ₗ (Q * P) + (R * P) where
  toLens := (fun ⟨qr, p⟩ => Sum.elim (fun q => Sum.inl (q, p)) (fun r => Sum.inr (r, p)) qr) ⇆
            (fun ⟨qr, p⟩ => match qr with
              | Sum.inl _ => id
              | Sum.inr _ => id)
  invLens := (fun qp_rp => match qp_rp with
              | Sum.inl (q, p) => (Sum.inl q, p)
              | Sum.inr (r, p) => (Sum.inr r, p)) ⇆
             (fun qp_rp => match qp_rp with
              | Sum.inl _ => id
              | Sum.inr _ => id)
  left_inv := by
    ext a <;> rcases a with ⟨q | r, p⟩ <;> rfl
  right_inv := by
    ext a <;> rcases a with ⟨q, p⟩ | ⟨r, p⟩ <;> rfl

end Equiv

end Prod

section Comp

@[simp]
theorem compMap_id {P Q : PFunctor.{u}} :
    (Lens.id P) ◂ₗ (Lens.id Q) = Lens.id (P ◂ Q) := by
  ext ⟨_, _⟩ ⟨_, _⟩ <;> rfl

theorem compMap_comp {P Q R P' Q' R' : PFunctor.{u}}
    (l₁ : Lens P P') (l₂ : Lens Q Q') (l₁' : Lens P' R) (l₂' : Lens Q' R') :
    (l₁' ∘ₗ l₁) ◂ₗ (l₂' ∘ₗ l₂) = (l₁' ◂ₗ l₂') ∘ₗ (l₁ ◂ₗ l₂) := rfl

namespace Equiv

/-- Associativity of composition -/
def compAssoc {P Q R : PFunctor.{u}} : (P ◂ Q) ◂ R ≃ₗ P ◂ (Q ◂ R) where
  toLens := (fun ⟨⟨pa, qf⟩, rf⟩ => ⟨pa, fun pb => ⟨qf pb, fun qb => rf ⟨pb, qb⟩⟩⟩) ⇆
            (fun _ ⟨pb, ⟨qb, rb⟩⟩ => ⟨⟨pb, qb⟩, rb⟩)
  invLens := (fun ⟨pa, g⟩ => ⟨⟨pa, fun pb => (g pb).1⟩, fun ⟨pb, qb⟩ => (g pb).2 qb⟩) ⇆
             (fun _ ⟨⟨pb, qb⟩, rb⟩ => ⟨pb, ⟨qb, rb⟩⟩)
  left_inv := rfl
  right_inv := rfl

/-- Composition with `y` is identity (right) -/
def compY {P : PFunctor.{u}} : P ◂ y ≃ₗ P where
  toLens := invTildeR
  invLens := tildeR
  left_inv := rfl
  right_inv := rfl

/-- Composition with `y` is identity (left) -/
def yComp {P : PFunctor.{u}} : y ◂ P ≃ₗ P where
  toLens := invTildeL
  invLens := tildeL
  left_inv := rfl
  right_inv := rfl

/-- Distributivity of composition over coproduct on the right -/
def coprodCompDistrib {P Q R : PFunctor.{u}} : (Q + R) ◂ P ≃ₗ (Q ◂ P) + (R ◂ P) where
  toLens := (fun a => match a with
              | ⟨Sum.inl qa, pf⟩ => Sum.inl ⟨qa, pf⟩
              | ⟨Sum.inr ra, pf⟩ => Sum.inr ⟨ra, pf⟩) ⇆
            (fun ⟨qr, pf⟩ b => match qr with
              | Sum.inl _ => b
              | Sum.inr _ => b)
  invLens := (fun a => match a with
              | Sum.inl ⟨qa, pf⟩ => ⟨Sum.inl qa, pf⟩
              | Sum.inr ⟨ra, pf⟩ => ⟨Sum.inr ra, pf⟩) ⇆
            (fun qprp b => match qprp with
              | Sum.inl _ => b
              | Sum.inr _ => b)
  left_inv := by
    ext a <;> rcases a with ⟨_ | _, _⟩ <;> rfl
  right_inv := by
    ext a <;> cases a <;> rfl

end Equiv

end Comp

section Tensor

@[simp]
theorem tensorMap_id {P Q : PFunctor.{u}} : (Lens.id P) ⊗ₗ (Lens.id Q) = Lens.id (P ⊗ₚ Q) :=
  rfl

theorem tensorMap_comp {P Q R P' Q' R' : PFunctor.{u}}
    (l₁ : Lens P P') (l₂ : Lens Q Q') (l₁' : Lens P' R) (l₂' : Lens Q' R') :
    (l₁' ∘ₗ l₁) ⊗ₗ (l₂' ∘ₗ l₂) = (l₁' ⊗ₗ l₂') ∘ₗ (l₁ ⊗ₗ l₂) := rfl

namespace Equiv

/-- Commutativity of tensor product -/
def tensorComm (P Q : PFunctor.{u}) : P ⊗ₚ Q ≃ₗ Q ⊗ₚ P where
  toLens := Prod.swap ⇆ (fun _ => Prod.swap)
  invLens := Prod.swap ⇆ (fun _ => Prod.swap)
  left_inv := rfl
  right_inv := rfl

/-- Associativity of tensor product -/
def tensorAssoc {P Q R : PFunctor.{u}} : (P ⊗ₚ Q) ⊗ₚ R ≃ₗ P ⊗ₚ (Q ⊗ₚ R) where
  toLens := (_root_.Equiv.prodAssoc _ _ _).toFun ⇆
            (fun _ => (_root_.Equiv.prodAssoc _ _ _).invFun)
  invLens := (_root_.Equiv.prodAssoc _ _ _).invFun ⇆
            (fun _ => (_root_.Equiv.prodAssoc _ _ _).toFun)
  left_inv := rfl
  right_inv := rfl

/-- Tensor product with `y` is identity (right) -/
def tensorY {P : PFunctor.{u}} : P ⊗ₚ y ≃ₗ P where
  toLens := Prod.fst ⇆ (fun _ b => (b, PUnit.unit))
  invLens := (fun p => (p, PUnit.unit)) ⇆ (fun _ bp => bp.1)
  left_inv := rfl
  right_inv := rfl

/-- Tensor product with `y` is identity (left) -/
def yTensor {P : PFunctor.{u}} : y ⊗ₚ P ≃ₗ P where
  toLens := Prod.snd ⇆ (fun _ b => (PUnit.unit, b))
  invLens := (fun p => (PUnit.unit, p)) ⇆ (fun _ bp => bp.2)
  left_inv := rfl
  right_inv := rfl

/-- Tensor product with `0` is zero (left) -/
def zeroTensor {P : PFunctor.{u}} : 0 ⊗ₚ P ≃ₗ 0 where
  toLens := (fun a => PEmpty.elim a.1) ⇆ (fun _ b => PEmpty.elim b)
  invLens := PEmpty.elim ⇆ (fun a _ => PEmpty.elim a)
  left_inv := by
    ext ⟨a, _⟩ <;> exact PEmpty.elim a
  right_inv := by
    ext a <;> exact PEmpty.elim a

/-- Tensor product with `0` is zero (right) -/
def tensorZero {P : PFunctor.{u}} : P ⊗ₚ 0 ≃ₗ 0 where
  toLens := (fun a => PEmpty.elim a.2) ⇆ (fun _ b => PEmpty.elim b)
  invLens := PEmpty.elim ⇆ (fun a _ => PEmpty.elim a)
  left_inv := by
    ext ⟨_, b⟩ <;> exact PEmpty.elim b
  right_inv := by
    ext a <;> exact PEmpty.elim a

/-- Left distributivity of tensor product over coproduct -/
def tensorCoprodDistrib {P Q R : PFunctor.{u}} : P ⊗ₚ (Q + R) ≃ₗ (P ⊗ₚ Q) + (P ⊗ₚ R) where
  toLens := (fun ⟨p, qr⟩ => match qr with
              | Sum.inl q => Sum.inl (p, q)
              | Sum.inr r => Sum.inr (p, r)) ⇆
            (fun ⟨p, qr⟩ b => match qr with
              | Sum.inl _ => b
              | Sum.inr _ => b)
  invLens := (fun pqpr => match pqpr with
              | Sum.inl (p, q) => (p, Sum.inl q)
              | Sum.inr (p, r) => (p, Sum.inr r)) ⇆
             (fun pqpr b => match pqpr with
              | Sum.inl _ => b
              | Sum.inr _ => b)
  left_inv := by
    ext ⟨_, qr⟩ <;> cases qr <;> rfl
  right_inv := by
    ext pqpr <;> cases pqpr <;> rfl

/-- Right distributivity of tensor product over coproduct -/
def coprodTensorDistrib {P Q R : PFunctor.{u}} : (Q + R) ⊗ₚ P ≃ₗ (Q ⊗ₚ P) + (R ⊗ₚ P) where
  toLens := (fun ⟨qr, p⟩ => match qr with
              | Sum.inl q => Sum.inl (q, p)
              | Sum.inr r => Sum.inr (r, p)) ⇆
            (fun ⟨qr, _⟩ b => match qr with
              | Sum.inl _ => b
              | Sum.inr _ => b)
  invLens := (fun qprp => match qprp with
              | Sum.inl (q, p) => (Sum.inl q, p)
              | Sum.inr (r, p) => (Sum.inr r, p)) ⇆
             (fun qprp b => match qprp with
              | Sum.inl _ => b
              | Sum.inr _ => b)
  left_inv := by
    ext ⟨qr, _⟩ <;> cases qr <;> rfl
  right_inv := by
    ext qprp <;> cases qprp <;> rfl

end Equiv

end Tensor

section Sigma

variable {I : Type v}

instance [IsEmpty I] {F : I → PFunctor.{u}} : IsEmpty (sigma F).A := by
  simp [sigma]
instance [IsEmpty I] {F : I → PFunctor.{u}} {a : (sigma F).A} : IsEmpty ((sigma F).B a) :=
  isEmptyElim a

/-- Sigma of an empty family is the zero functor. -/
def sigmaEmpty [IsEmpty I] {F : I → PFunctor.{u}} : sigma F ≃ₗ 0 where
  toLens := isEmptyElim ⇆ (fun a _ => isEmptyElim a)
  invLens := isEmptyElim ⇆ (fun a _ => isEmptyElim a)
  left_inv := by ext a <;> exact isEmptyElim a
  right_inv := by ext a <;> exact isEmptyElim a

/-- Sigma of a `PUnit`-indexed family is equivalent to the functor itself. -/
def sigmaUnit {F : PUnit → PFunctor.{u}} : sigma F ≃ₗ (F PUnit.unit).ulift where
  toLens := (fun ⟨_, a⟩ => ULift.up a) ⇆ (fun _ b => b)
  invLens := (fun a => ⟨PUnit.unit, ULift.down a⟩) ⇆ (fun _ b => b)
  left_inv := rfl
  right_inv := rfl

/-- Sigma of an `I`-indexed family, where `I` is unique, is equivalent to the functor itself. -/
def sigmaOfUnique [Unique I] {F : I → PFunctor.{u}} : sigma F ≃ₗ (F default).ulift where
  toLens := (fun ⟨_, a⟩ => (Unique.uniq _ _) ▸ ULift.up a) ⇆
            (fun ⟨i, a⟩ b => (Unique.uniq _ i) ▸ b)
  invLens := (fun a => ⟨default, ULift.down a⟩) ⇆ (fun _ b => b)
  left_inv := by
    ext ⟨i, a⟩ b <;> simp [sigma, Lens.id, comp]
    · generalize_proofs h; subst h; simp
    · generalize_proofs _ h; subst h; simp
  right_inv := rfl

/-- Left distributivity of product over sigma. -/
def prodSigmaDistrib {P : PFunctor.{u}} {I : Type u} {F : I → PFunctor.{u}} :
    P * sigma F ≃ₗ sigma (fun i => P * F i) where
  toLens := (fun ⟨pa, ⟨i, fia⟩⟩ => ⟨i, ⟨pa, fia⟩⟩) ⇆
            (fun _ b => match ULift.down b with
              | Sum.inl p => Sum.inl p
              | Sum.inr q => Sum.inr (ULift.up q))
  invLens := (fun ⟨i, ⟨pa, fia⟩⟩ => ⟨pa, ⟨i, fia⟩⟩) ⇆
             (fun _ b => match b with
              | Sum.inl p => ULift.up (Sum.inl p)
              | Sum.inr q => ULift.up (Sum.inr (ULift.down q)))
  left_inv := by
    ext ⟨pa, ⟨i, fia⟩⟩ b
    · rfl
    · rcases b with _ | _ <;> rfl
  right_inv := by
    ext ⟨i, ⟨pa, fia⟩⟩ b
    · rfl
    · rcases b with _ | _ <;> rfl

/-- Right distributivity of product over sigma. -/
def sigmaProdDistrib {P : PFunctor.{u}} {I : Type u} {F : I → PFunctor.{u}} :
    sigma F * P ≃ₗ sigma (fun i => F i * P) where
  toLens := (fun ⟨⟨i, fia⟩, pa⟩ => ⟨i, ⟨fia, pa⟩⟩) ⇆
            (fun _ b => match ULift.down b with
              | Sum.inl p => Sum.inl (ULift.up p)
              | Sum.inr q => Sum.inr q)
  invLens := (fun ⟨i, ⟨fia, pa⟩⟩ => ⟨⟨i, fia⟩, pa⟩) ⇆
             (fun _ b => match b with
              | Sum.inl p => ULift.up (Sum.inl (ULift.down p))
              | Sum.inr q => ULift.up (Sum.inr q))
  left_inv := by
    ext ⟨⟨i, fia⟩, pa⟩ b
    · rfl
    · rcases b with _ | _ <;> rfl
  right_inv := by
    ext ⟨i, ⟨fia, pa⟩⟩ b
    · rfl
    · rcases b with _ | _ <;> rfl

/-- Left distributivity of tensor product over sigma. -/
def tensorSigmaDistrib {P : PFunctor.{u}} {I : Type u} {F : I → PFunctor.{u}} :
    P ⊗ₚ sigma F ≃ₗ sigma (fun i => P ⊗ₚ F i) where
  toLens := (fun ⟨pa, ⟨i, fia⟩⟩ => ⟨i, ⟨pa, fia⟩⟩) ⇆
            (fun _ ⟨pb, fib⟩ => ⟨pb, ULift.up fib⟩)
  invLens := (fun ⟨i, ⟨pa, fia⟩⟩ => ⟨pa, ⟨i, fia⟩⟩) ⇆
             (fun _ ⟨pb, fib⟩ => ⟨pb, ULift.down fib⟩)
  left_inv := rfl
  right_inv := rfl

/-- Right distributivity of tensor product over sigma. -/
def sigmaTensorDistrib {P : PFunctor.{u}} {I : Type u} {F : I → PFunctor.{u}} :
    sigma F ⊗ₚ P ≃ₗ sigma (fun i => F i ⊗ₚ P) where
  toLens := (fun ⟨⟨i, fia⟩, pa⟩ => ⟨i, ⟨fia, pa⟩⟩) ⇆
            (fun _ ⟨fib, pb⟩ => ⟨ULift.up fib, pb⟩)
  invLens := (fun ⟨i, ⟨fia, pa⟩⟩ => ⟨⟨i, fia⟩, pa⟩) ⇆
             (fun _ ⟨fib, pb⟩ => ⟨ULift.down fib, pb⟩)
  left_inv := rfl
  right_inv := rfl

-- /-- Right distributivity of composition over sigma. -/
-- def sigmaCompDistrib {P : PFunctor.{u}} {I : Type u} {F : I → PFunctor.{u}} :
--     (sigma F) ◂ P ≃ₗ sigma (fun i => F i ◂ P) where
--   toLens := (fun ⟨⟨i, fia⟩, pf⟩ => ⟨i, ⟨fia, pf⟩⟩) ⇆
--             (fun _ b => match ULift.down b with
--               | Sum.inl p => Sum.inl (ULift.up p)
--               | Sum.inr q => Sum.inr q)
--   invLens := (fun ⟨i, ⟨fia, pf⟩⟩ => ⟨⟨i, fia⟩, pf⟩) ⇆
--              (fun _ b => match b with
--               | Sum.inl p => ULift.up (Sum.inl (ULift.down p))
--               | Sum.inr q => ULift.up (Sum.inr q))
--   left_inv := rfl
--   right_inv := rfl

end Sigma

section Pi

variable {I : Type v}

/-- Pi over a `PUnit`-indexed family is equivalent to the functor itself. -/
def piUnit {P : PFunctor.{u}} : pi (fun (_ : PUnit) => P) ≃ₗ P where
  toLens := (fun f => f PUnit.unit) ⇆ (fun _ pb => ⟨PUnit.unit, pb⟩)
  invLens := (fun pa _ => pa) ⇆ (fun _ spb => spb.2)
  left_inv := rfl
  right_inv := rfl

-- /-- Pi of a family of zero functors over an inhabited type is the zero functor. -/
-- def piZero (F_zero : ∀ i, F i = 0) :
--     pi (F : I → PFunctor.{u}) ≃ₗ 0 where
--   toLens := (fun a => PEmpty.elim (Classical.choice (Function.funext_iff.mp F_zero (Classical.choice Classical.propDecidable)))) ⇆ -- Requires some work to construct the PEmpty element
--             (fun _ => PEmpty.elim)
--   invLens := PEmpty.elim ⇆ (fun a => PEmpty.elim a)
--   left_inv := sorry -- Proof depends on constructing the PEmpty term above
--   right_inv := by ext a <;> exact PEmpty.elim a

end Pi

end Lens

-- Do the same for charts?

end Lemmas

end PFunctor
