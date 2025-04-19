import Mathlib.Data.PFunctor.Multivariate.Basic

/-!
  # Polynomial Functors

  We want to define a bunch of missing definitions for polynomial functors, with a view towards
  defining the free monad on a polynomial functor (which does not raise the universe level), and
  also to model interactive protocols.
-/

universe u v

namespace PFunctor

-- Define operations on `PFunctor`s: sum, product, composition, tensor product, function space (lolli), etc.

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

/-- Infix notation for monomial `A y^B` -/
infixr:80 " y^" => monomial

/-- The constant functor `P(y) = A` -/
def C (A : Type u) : PFunctor.{u} :=
  monomial A PEmpty

@[simp]
theorem C_zero : C PEmpty = 0 := rfl

@[simp]
theorem C_one : C PUnit = 1 := rfl

/-- The self monomial functor `P(y) = S y^S` -/
def selfMonomial (S : Type u) : PFunctor.{u} := S y^S

/-- The pure power functor `P(y) = y^B` -/
def purePower (B : Type u) : PFunctor.{u} :=
  monomial PUnit B

/-- A polynomial functor is representable if it is equivalent to `y^A` for some type `A`. -/
alias representable := purePower

/-- The linear functor `P(y) = A y` -/
def linear (A : Type u) : PFunctor.{u} :=
  monomial A PUnit

/-- Infix notation for `PFunctor.comp P Q` -/
infixl:80 " ◂ " => PFunctor.comp

/-- The unit for composition `Y` -/
@[reducible]
def compositionUnit : PFunctor.{u} := y

/-- Repeated composition `P ◂ P ◂ ... ◂ P` (n times). -/
@[simp]
def compositePower (P : PFunctor.{u}) : Nat → PFunctor.{u}
  | 0 => compositionUnit
  | n + 1 => P ◂ compositePower P n

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

/-- Infix notation for lens composition `l' ∘ₚ l` -/
infixl:25 " ∘ₚ " => comp

/-- The unique lens from the zero functor to any functor `P`. -/
def zero {P : PFunctor.{u}} : Lens 0 P :=
  PEmpty.elim ⇆ fun a => PEmpty.elim a

/-- Apply lenses to both sides of a composition: `(P → R) → (Q → W) → (P ◂ Q → R ◂ W)` -/
def compMap {P Q R W : PFunctor.{u}} (l₁ : Lens P R) (l₂ : Lens Q W) : Lens (P ◂ Q) (R ◂ W) :=
  Lens.mk
    (fun ⟨pa, pq⟩ => ⟨l₁.mapPos pa, fun rb' => l₂.mapPos (pq (l₁.mapDir pa rb'))⟩)
    (fun ⟨pa, pq⟩ ⟨rb, wc⟩ =>
      let pb := l₁.mapDir pa rb
      let qc := l₂.mapDir (pq pb) wc
      ⟨pb, qc⟩)

/-- Infix notation for `compMap` -/
infixl:75 " ⟨◂⟩ " => compMap

/-- Lens to introduce `Y` on the right: `C → C ◂ Y` -/
def tilde_r {P : PFunctor.{u}} : Lens P (P ◂ y) :=
  (fun a => ⟨a, fun _ => PUnit.unit⟩) ⇆ (fun _a => fun ⟨b, _⟩ => b)

/-- Lens to introduce `Y` on the left: `C → Y ◂ C` -/
def tilde_l {P : PFunctor.{u}} : Lens P (y ◂ P) :=
  (fun a => ⟨PUnit.unit, fun _ => a⟩) ⇆ (fun _a => fun ⟨_, b⟩ => b)

/-- Helper lens for `speedup` -/
def fixState {S : Type u} : Lens (selfMonomial S) (selfMonomial S ◂ selfMonomial S) :=
  (fun s₀ => ⟨s₀, fun s₁ => s₁⟩) ⇆ (fun _s₀ => fun ⟨_s₁, s₂⟩ => s₂)

/-- The `speedup` lens operation: `Lens (S y^S) P → Lens (S y^S) (P ◂ P)` -/
def speedup {S : Type u} {P : PFunctor.{u}} (l : Lens (selfMonomial S) P) :
    Lens (selfMonomial S) (P ◂ P) :=
  let dup := l ⟨◂⟩ l
  Lens.comp dup fixState

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

/-- The unique chart from the zero functor to any functor `P`. -/
def zero {P : PFunctor.{u}} : Chart 0 P :=
  PEmpty.elim ⇉ fun _ => PEmpty.elim

end Chart

end PFunctor

-- TODO: how is the free monad itself a PFunctor?

-- Prove theorems about the interaction between operations on `PFunctor`s
