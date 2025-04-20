import Mathlib.Data.PFunctor.Multivariate.Basic

/-!
  # Polynomial Functors

  We want to define a bunch of missing definitions for polynomial functors, with a view towards
  defining the free monad on a polynomial functor (which does not raise the universe level), and
  also to model interactive protocols.
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

section Product

/-- Product of polynomial functors `P * Q` -/
def prod (P Q : PFunctor.{u}) : PFunctor.{u} :=
  ⟨P.A × Q.A, fun ab => P.B ab.1 ⊕ Q.B ab.2⟩

instance : Mul PFunctor.{u} where
  mul := prod

alias prodUnit := one

/-- Generalized product (pi type) of an indexed family of polynomial functors -/
def pi {I : Type v} (F : I → PFunctor.{u}) : PFunctor.{max u v} :=
  ⟨(i : I) → (F i).A, fun f => Σ i, (F i).B (f i)⟩

end Product

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

/-- The linear functor `P(y) = A y` -/
def linear (A : Type u) : PFunctor.{u} :=
  monomial A PUnit

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

/-- The (unique) initial lens from the zero functor to any functor `P`. -/
def initial {P : PFunctor.{u}} : Lens 0 P :=
  PEmpty.elim ⇆ fun a => PEmpty.elim a

/-- The (unique) terminal lens from any functor `P` to the unit functor `1`. -/
def terminal {P : PFunctor.{u}} : Lens P 1 :=
  (fun _ => PUnit.unit) ⇆ (fun _ => PEmpty.elim)

alias fromZero := initial
alias toOne := terminal

/-- Projection lens `π₁ : P * Q → P` -/
def pi1 {P Q : PFunctor.{u}} : Lens (P * Q) P :=
  Prod.fst ⇆ (fun _ => Sum.inl)

/-- Projection lens `π₂ : P * Q → Q` -/
def pi2 {P Q : PFunctor.{u}} : Lens (P * Q) Q :=
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

@[inherit_doc] infixl:25 " ∘ₚ " => comp
@[inherit_doc] infixl:75 " ⟨◂⟩ " => compMap
@[inherit_doc] infixl:75 " ⟨×⟩ " => prodMap
@[inherit_doc] infixl:75 " ⟨×⟩ " => prodMap
@[inherit_doc] infixl:75 " ⟨⊎⟩ " => coprodMap
@[inherit_doc] infixl:75 " ⟨⊗⟩ " => tensorMap
notation "~ᴿ" => tildeR
notation "~ᴸ" => tildeL
notation "[" l₁ "," l₂ "]ₚ" => coprodPair l₁ l₂


/-- The type of lenses from P to Y -/
def enclose (P : PFunctor.{u}) : Type u :=
  Lens P y

/-- Helper lens for `speedup` -/
def fixState {S : Type u} : Lens (selfMonomial S) (selfMonomial S ◂ selfMonomial S) :=
  (fun s₀ => ⟨s₀, fun s₁ => s₁⟩) ⇆ (fun _s₀ => fun ⟨_s₁, s₂⟩ => s₂)

/-- The `speedup` lens operation: `Lens (S y^S) P → Lens (S y^S) (P ◂ P)` -/
def speedup {S : Type u} {P : PFunctor.{u}} (l : Lens (selfMonomial S) P) :
    Lens (selfMonomial S) (P ◂ P) :=
  (l ⟨◂⟩ l) ∘ₚ fixState

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

/-- The (unique) initial chart from the zero functor to any functor `P`. -/
def initial {P : PFunctor.{u}} : Chart 0 P :=
  PEmpty.elim ⇉ fun _ => PEmpty.elim

/-- The (unique) terminal chart from any functor `P` to the functor `Y`. -/
def terminal {P : PFunctor.{u}} : Chart P y :=
  (fun _ => PUnit.unit) ⇉ (fun _ _ => PUnit.unit)

alias fromZero := initial
alias toOne := terminal

end Chart

end PFunctor

-- TODO: how is the free monad itself a PFunctor?

-- Prove theorems about the interaction between operations on `PFunctor`s
