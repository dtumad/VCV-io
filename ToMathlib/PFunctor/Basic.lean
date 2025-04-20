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

/-- The zero polynomial functor -/
def zero : PFunctor.{u} := ⟨PEmpty, fun _ => PEmpty⟩

/-- The unit polynomial functor -/
def one : PFunctor.{u} := ⟨PUnit, fun _ => PEmpty⟩

instance : Zero PFunctor.{u} where
  zero := zero

instance : One PFunctor.{u} where
  one := one

/-- The variable `y` polynomial functor -/
def y : PFunctor.{u} :=
  ⟨PUnit, fun _ => PUnit⟩

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

section Coprod

/-- Coprod (sum) of polynomial functors `P + Q` -/
def coprod (P Q : PFunctor.{u}) : PFunctor.{u} :=
  ⟨P.A ⊕ Q.A, Sum.elim P.B Q.B⟩

instance : Add PFunctor.{u} where
  add := coprod

alias coprodUnit := zero

/-- Generalized coproduct (sigma type) of an indexed family of polynomial functors -/
def sigma {I : Type u} (F : I → PFunctor.{u}) : PFunctor.{u} :=
  ⟨Σ i, (F i).A, fun ⟨i, a⟩ => (F i).B a⟩

end Coprod

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

/-- Tensor or parallel prod of polynomial functors -/
def tensor (P Q : PFunctor.{u}) : PFunctor.{u} :=
  ⟨P.A × Q.A, fun ab => P.B ab.1 × Q.B ab.2⟩

/-- Infix notation for tensor prod `P ⊗ₚ Q` -/
infixl:70 " ⊗ₚ " => tensor

/-- The unit for the tensor prod `Y` -/
alias tensorUnit := y

end Tensor

/-- A lens between two polynomial functors `P` and `Q` is a pair of a function:
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

@[inherit_doc] infixl:25 " ∘ₗ " => comp

/-- An equivalence between two polynomial functors `P` and `Q`, using lenses.
    This corresponds to an isomorphism in the category `PFunctor` with `Lens` morphisms. -/
@[ext]
structure Equiv (P Q : PFunctor.{u}) where
  toLens : Lens P Q
  invLens : Lens Q P
  left_inv : comp invLens toLens = Lens.id P
  right_inv : comp toLens invLens = Lens.id Q

@[inherit_doc] infix:25 " ≃ₗ " => Equiv

namespace Equiv

@[refl]
def refl (P : PFunctor.{u}) : P ≃ₗ P :=
  ⟨Lens.id P, Lens.id P, rfl, rfl⟩

@[symm]
def symm {P Q : PFunctor.{u}} (e : P ≃ₗ Q) : Q ≃ₗ P :=
  ⟨e.invLens, e.toLens, e.right_inv, e.left_inv⟩

@[trans]
def trans {P Q R : PFunctor.{u}} (e₁ : P ≃ₗ Q) (e₂ : Q ≃ₗ R) : P ≃ₗ R :=
  ⟨e₂.toLens ∘ₗ e₁.toLens, e₁.invLens ∘ₗ e₂.invLens, by
    sorry,
    sorry⟩

end Equiv

/-- The (unique) initial lens from the zero functor to any functor `P`. -/
def initial {P : PFunctor.{u}} : Lens 0 P :=
  PEmpty.elim ⇆ fun a => PEmpty.elim a

/-- The (unique) terminal lens from any functor `P` to the unit functor `1`. -/
def terminal {P : PFunctor.{u}} : Lens P 1 :=
  (fun _ => PUnit.unit) ⇆ (fun _ => PEmpty.elim)

alias fromZero := initial
alias toOne := terminal

/-- Projection lens `π₁ : P * Q → P` -/
def fst {P Q : PFunctor.{u}} : Lens (P * Q) P :=
  Prod.fst ⇆ (fun _ => Sum.inl)

/-- Projection lens `π₂ : P * Q → Q` -/
def snd {P Q : PFunctor.{u}} : Lens (P * Q) Q :=
  Prod.snd ⇆ (fun _ => Sum.inr)

/-- Pairing of lenses `⟨l₁, l₂⟩ : P → Q * R` -/
def prodPair {P Q R : PFunctor.{u}} (l₁ : Lens P Q) (l₂ : Lens P R) : Lens P (Q * R) :=
  (fun p => (l₁.mapPos p, l₂.mapPos p)) ⇆
    (fun p => Sum.elim (l₁.mapDir p) (l₂.mapDir p))

/-- Parallel application of lenses for prod `⟨l₁ × l₂⟩ : P * Q → R * W` -/
def prodMap {P Q R W : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q W) : Lens (P * Q) (R * W) :=
  (fun pq => (l₁.mapPos pq.1, l₂.mapPos pq.2)) ⇆
    (fun pq => Sum.elim (Sum.inl ∘ l₁.mapDir pq.1) (Sum.inr ∘ l₂.mapDir pq.2))

/-- Left injection lens `i₁ : P → P + Q` -/
def inl {P Q : PFunctor.{u}} : Lens P (P + Q) :=
  Sum.inl ⇆ (fun _ d => d)

/-- Right injection lens `i₂ : Q → P + Q` -/
def inr {P Q : PFunctor.{u}} : Lens Q (P + Q) :=
  Sum.inr ⇆ (fun _ d => d)

/-- Copairing of lenses `[l₁, l₂]ₚ : P + Q → R` -/
def coprodPair {P Q R : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q R) : Lens (P + Q) R :=
  (Sum.elim l₁.mapPos l₂.mapPos) ⇆
    (fun a d => match a with
      | Sum.inl pa => l₁.mapDir pa d
      | Sum.inr qa => l₂.mapDir qa d)

/-- Parallel application of lenses for coprod `⟨l₁ ⊎ l₂⟩ : P + Q → R + W` -/
def coprodMap {P Q R W : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q W) : Lens (P + Q) (R + W) :=
  (Sum.map l₁.mapPos l₂.mapPos) ⇆
    (fun psum => match psum with
      | Sum.inl pa => l₁.mapDir pa
      | Sum.inr qa => l₂.mapDir qa)

/-- Apply lenses to both sides of a composition: `(P ⇆ R) → (Q ⇆ W) → (P ◂ Q ⇆ R ◂ W)` -/
def compMap {P Q R W : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q W) : Lens (P ◂ Q) (R ◂ W) :=
  (fun ⟨pa, pq⟩ => ⟨l₁.mapPos pa, fun rb' => l₂.mapPos (pq (l₁.mapDir pa rb'))⟩) ⇆
    (fun ⟨pa, pq⟩ ⟨rb, wc⟩ =>
      let pb := l₁.mapDir pa rb
      let qc := l₂.mapDir (pq pb) wc
      ⟨pb, qc⟩)

/-- Apply lenses to both sides of a tensor prod: `(P ⇆ R) → (Q ⇆ W) → (P ⊗ₚ Q ⇆ R ⊗ₚ W)` -/
def tensorMap {P Q R W : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q W) : Lens (P ⊗ₚ Q) (R ⊗ₚ W) :=
  (fun ⟨pa, qa⟩ => (l₁.mapPos pa, l₂.mapPos qa)) ⇆
    (fun ⟨_pa, qa⟩ ⟨rb, wb⟩ => (l₁.mapDir _pa rb, l₂.mapDir qa wb))

/-- Lens to introduce `Y` on the right: `C → C ◂ Y` -/
def tildeR {P : PFunctor.{u}} : Lens P (P ◂ y) :=
  (fun a => ⟨a, fun _ => PUnit.unit⟩) ⇆ (fun _a => fun ⟨b, _⟩ => b)

/-- Lens to introduce `Y` on the left: `C → Y ◂ C` -/
def tildeL {P : PFunctor.{u}} : Lens P (y ◂ P) :=
  (fun a => ⟨PUnit.unit, fun _ => a⟩) ⇆ (fun _a => fun ⟨_, b⟩ => b)

@[inherit_doc] infixl:75 " ⟨◂⟩ " => compMap
@[inherit_doc] infixl:75 " ⟨×⟩ " => prodMap
@[inherit_doc] infixl:75 " ⟨×⟩ " => prodMap
@[inherit_doc] infixl:75 " ⟨⊎⟩ " => coprodMap
@[inherit_doc] infixl:75 " ⟨⊗⟩ " => tensorMap
notation "~ᴿ" => tildeR
notation "~ᴸ" => tildeL
notation "[" l₁ "," l₂ "]ₚ" => coprodPair l₁ l₂

/-- The type of lenses from a polynomial functor `P` to `y` -/
def enclose (P : PFunctor.{u}) : Type u :=
  Lens P y

/-- Helper lens for `speedup` -/
def fixState {S : Type u} : Lens (selfMonomial S) (selfMonomial S ◂ selfMonomial S) :=
  (fun s₀ => ⟨s₀, fun s₁ => s₁⟩) ⇆ (fun _s₀ => fun ⟨_s₁, s₂⟩ => s₂)

/-- The `speedup` lens operation: `Lens (S y^S) P → Lens (S y^S) (P ◂ P)` -/
def speedup {S : Type u} {P : PFunctor.{u}} (l : Lens (selfMonomial S) P) :
    Lens (selfMonomial S) (P ◂ P) :=
  (l ⟨◂⟩ l) ∘ₗ fixState

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
infixl:25 " ∘c " => comp

/-- An equivalence between two polynomial functors `P` and `Q`, using charts.
    This corresponds to an isomorphism in the category `PFunctor` with `Chart` morphisms. -/
@[ext]
structure Equiv (P Q : PFunctor.{u}) where
  toChart : Chart P Q
  invChart : Chart Q P
  left_inv : comp invChart toChart = Chart.id P
  right_inv : comp toChart invChart = Chart.id Q

/-- Infix notation for chart equivalence `P ≃c Q` -/
infix:25 " ≃c " => Equiv

namespace Equiv

@[refl]
def refl (P : PFunctor.{u}) : P ≃c P :=
  ⟨Chart.id P, Chart.id P, rfl, rfl⟩

@[symm]
def symm {P Q : PFunctor.{u}} (e : P ≃c Q) : Q ≃c P :=
  ⟨e.invChart, e.toChart, e.right_inv, e.left_inv⟩

def trans {P Q R : PFunctor.{u}} (e₁ : P ≃c Q) (e₂ : Q ≃c R) : P ≃c R :=
  ⟨e₂.toChart ∘c e₁.toChart, e₁.invChart ∘c e₂.invChart,
    sorry,
    sorry⟩

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

-- We can now prove basic properties about the operations on `PFunctor`s

@[ext (iff := false)]
theorem ext {P Q : PFunctor.{u}} (h : P.A = Q.A) (h' : ∀ a, P.B a = Q.B (h ▸ a)) : P = Q := by
  cases P; cases Q; simp at h h' ⊢; subst h; simp_all; funext; exact h' _

@[ext (iff := false)]
theorem Lens.ext {P Q : PFunctor.{u}} (l₁ l₂ : Lens P Q)
    (h₁ : l₁.mapPos = l₂.mapPos) (h₂ : l₁.mapDir = h₁ ▸ l₂.mapDir) : l₁ = l₂ := by
  cases l₁; cases l₂
  simp only at h₁
  subst h₁
  simp_all

@[ext (iff := false)]
theorem Chart.ext {P Q : PFunctor.{u}} (c₁ c₂ : Chart P Q)
    (h₁ : c₁.mapPos = c₂.mapPos) (h₂ : c₁.mapDir = h₁ ▸ c₂.mapDir) : c₁ = c₂ := by
  cases c₁; cases c₂
  simp only at h₁
  subst h₁
  simp_all

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

section Prod

namespace Lens.Equiv

/-- Commutativity of product -/
def prodComm (P Q : PFunctor.{u}) : P * Q ≃ₗ Q * P where
  toLens := Prod.swap ⇆ (fun _ => Sum.elim Sum.inr Sum.inl)
  invLens := Prod.swap ⇆ (fun _ => Sum.elim Sum.inr Sum.inl)
  left_inv := sorry -- by apply Lens.ext; simp; funext a d; simp; cases d <;> rfl
  right_inv := sorry -- by apply Lens.ext; simp; funext a d; simp; cases d <;> rfl

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
  left_inv := sorry
  right_inv := sorry

/-- Product with `1` is identity (left) -/
def oneProd {P : PFunctor.{u}} : 1 * P ≃ₗ P where
  toLens := Prod.snd ⇆ (fun _ => Sum.inr)
  invLens := (fun p => (PUnit.unit, p)) ⇆ (fun _ => Sum.elim PEmpty.elim id)
  left_inv := sorry
  right_inv := sorry

/-- Product with `0` is zero (right) -/
def prodZero {P : PFunctor.{u}} : P * 0 ≃ₗ 0 where
  toLens := (fun ⟨_, pa⟩ => PEmpty.elim pa) ⇆ (fun pe _ => sorry)
  invLens := PEmpty.elim ⇆ (fun pe _ => PEmpty.elim pe)
  left_inv := sorry
  right_inv := sorry

/-- Product with `0` is zero (left) -/
def zeroProd {P : PFunctor.{u}} : 0 * P ≃ₗ 0 where
  toLens := (fun ⟨pa, _⟩ => PEmpty.elim pa) ⇆ (fun pe _ => sorry)
  invLens := PEmpty.elim ⇆ (fun pe _ => PEmpty.elim pe)
  left_inv := sorry
  right_inv := sorry

/-- Product distributes over coproduct (sum) -/
def prodCoprodDistrib {P Q R : PFunctor.{u}} : P * (Q + R) ≃ₗ (P * Q) + (P * R) where
  toLens := (fun ⟨p, qr⟩ => match qr with | Sum.inl q => Sum.inl (p, q) | Sum.inr r => Sum.inr (p, r)) ⇆
            (fun ⟨p, qr⟩ => match qr with
              | Sum.inl q => Sum.elim (Sum.inl ∘ sorry) (Sum.inl ∘ sorry)
              | Sum.inr r => Sum.elim (Sum.inr ∘ sorry) (Sum.inr ∘ sorry))
  invLens := (Sum.elim (fun ⟨p, q⟩ => (p, Sum.inl q)) (fun ⟨p, r⟩ => (p, Sum.inr r))) ⇆
             (fun pq_pr => match pq_pr with
              | Sum.inl ⟨p, q⟩ => fun s => match s with | Sum.inl pb => Sum.inl pb | Sum.inr qb => Sum.inr (sorry)
              | Sum.inr ⟨p, r⟩ => fun s => match s with | Sum.inl pb => Sum.inl pb | Sum.inr rb => Sum.inr (sorry))
  left_inv := sorry
  right_inv := sorry

end Lens.Equiv

end Prod

end Lemmas

end PFunctor
