/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.PFunctor.Basic

/-!
# Equivalences of Polynomial Functors

This file defines equivalences between polynomial functors and proves basic properties about them.

An equivalence between two polynomial functors `P` and `Q`, written `P ≃ₚ Q`, is given by an
equivalence of the `A` types and an equivalence between the `B` types for each `a : A`.

We provide various canonical equivalences for operations on polynomial functors, such as:
- Sum operations: `P + 0 ≃ₚ P`, `0 + P ≃ₚ P`
- Product operations and their properties
- Equivalences for sigma and pi constructions
- Universe lifting equivalences
- Tensor product equivalences
- Composition equivalences

## Main definitions

- `PFunctor.Equiv`: An equivalence between two polynomial functors
- `≃ₚ`: Notation for polynomial functor equivalences

## Main results

- Basic equivalence properties: reflexivity, symmetry, transitivity
- Canonical equivalences for sum, product, and other constructions on polynomial functors
-/

universe u v uA uB uA' uB' uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄

namespace PFunctor

namespace Equiv

section Sum

variable (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB})
  (R : PFunctor.{uA₃, uB}) (S : PFunctor.{uA₄, uB})

/-- Addition with the zero functor on the left is equivalent to the original functor -/
@[simps]
def sumZero : P + 0 ≃ₚ P where
  equivA := Equiv.sumEmpty P.A PEmpty
  equivB := fun a => {
      toFun := Sum.casesOn a (fun _ => id) (fun a => a.elim)
      invFun := Sum.casesOn a (fun _ => id) (fun a => a.elim)
      left_inv x := by rcases a with _ | a; simp; exact a.elim
      right_inv x := by rcases a with _ | a; simp; exact a.elim
    }

/-- Addition with the zero functor on the right is equivalent to the original functor -/
@[simps]
def zeroSum : 0 + P ≃ₚ P where
  equivA := Equiv.emptySum PEmpty P.A
  equivB := fun a => {
    toFun := Sum.casesOn a (fun a => a.elim) (fun _ => id)
    invFun := Sum.casesOn a (fun a => a.elim) (fun _ => id)
    left_inv x := by rcases a with a | _; exact a.elim; simp
    right_inv x := by rcases a with a | _; exact a.elim; simp
  }

/-- Sum of polynomial functors is commutative up to equivalence -/
@[simps]
def sumComm : (P + Q : PFunctor.{max uA₁ uA₂, uB}) ≃ₚ (Q + P : PFunctor.{max uA₁ uA₂, uB}) where
  equivA := _root_.Equiv.sumComm P.A Q.A
  equivB := fun a => {
    toFun := Sum.casesOn a (fun _ => id) (fun _ => id)
    invFun := Sum.casesOn a (fun _ => id) (fun _ => id)
    left_inv x := by rcases a with _ | _ <;> simp
    right_inv x := by rcases a with _ | _ <;> simp
  }

/-- Sum of polynomial functors is associative up to equivalence -/
@[simps]
def sumAssoc :
    ((P + Q) + R : PFunctor.{max uA₁ uA₂ uA₃, uB}) ≃ₚ
    (P + (Q + R) : PFunctor.{max uA₁ uA₂ uA₃, uB}) where
  equivA := _root_.Equiv.sumAssoc P.A Q.A R.A
  equivB := fun a => {
    toFun := Sum.casesOn a (Sum.casesOn · (fun _ => id) (fun _ => id)) (fun _ => id)
    invFun := Sum.casesOn a (Sum.casesOn · (fun _ => id) (fun _ => id)) (fun _ => id)
    left_inv x := by rcases a with (_ | _) | _ <;> simp
    right_inv x := by rcases a with (_ | _) | _ <;> simp
  }

/-- If `P ≃ₚ R` and `Q ≃ₚ S`, then `P + Q ≃ₚ R + S` -/
@[simps]
def sumCongr {P Q} {R : PFunctor.{uA₃, uB₁}} {S : PFunctor.{uA₄, uB₁}} (e₁ : P ≃ₚ R) (e₂ : Q ≃ₚ S) :
    P + Q ≃ₚ (R + S : PFunctor.{max uA₃ uA₄, uB₁}) where
  equivA := _root_.Equiv.sumCongr e₁.equivA e₂.equivA
  equivB := fun a => {
    toFun := Sum.casesOn a (e₁.equivB ·) (e₂.equivB ·)
    invFun := Sum.casesOn a (fun a => (e₁.equivB a).symm) (fun a => (e₂.equivB a).symm)
    left_inv x := by rcases a with _ | _ <;> simp
    right_inv x := by rcases a with _ | _ <;> simp
  }

/-- Rearrangement of nested sums: `(P + Q) + (R + S) ≃ₚ (P + R) + (Q + S)` -/
def sumSumSumComm :
    ((P + Q) + (R + S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, uB}) ≃ₚ
    ((P + R) + (Q + S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, uB}) where
  equivA := _root_.Equiv.sumSumSumComm P.A Q.A R.A S.A
  equivB := fun a => {
    toFun := Sum.casesOn a (Sum.casesOn · (fun _ => id) (fun _ => id))
      (Sum.casesOn · (fun _ => id) (fun _ => id))
    invFun := Sum.casesOn a (Sum.casesOn · (fun _ => id) (fun _ => id))
      (Sum.casesOn · (fun _ => id) (fun _ => id))
    left_inv x := by rcases a with (_ | _) | (_ | _) <;> simp
    right_inv x := by rcases a with (_ | _) | (_ | _) <;> simp
  }

end Sum

section Prod

variable (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (R : PFunctor.{uA₃, uB₃})
  (S : PFunctor.{uA₄, uB₄})

/-- Product with the unit functor on the right is equivalent to the original functor -/
@[simps]
def prodOne : P * 1 ≃ₚ P where
  equivA := _root_.Equiv.prodPUnit P.A
  equivB := fun a => {
    toFun := Sum.elim id (fun x => x.elim)
    invFun := Sum.inl
    left_inv x := by rcases x with x | x; simp; exact x.elim
  }

/-- Product with the unit functor on the left is equivalent to the original functor -/
@[simps]
def oneProd : 1 * P ≃ₚ P where
  equivA := _root_.Equiv.punitProd P.A
  equivB := fun a => {
    toFun := Sum.elim (fun x => x.elim) id
    invFun := Sum.inr
    left_inv x := by rcases x with x | x; exact x.elim; simp
  }

/-- Product of polynomial functors is commutative up to equivalence -/
@[simps]
def prodComm :
    (P * Q : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) ≃ₚ
    (Q * P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) where
  equivA := _root_.Equiv.prodComm P.A Q.A
  equivB := fun a => {
    toFun := Sum.swap
    invFun := Sum.swap
    left_inv x := by rcases x with _ | _ <;> simp
    right_inv x := by rcases x with _ | _ <;> simp
  }

/-- Product of polynomial functors is associative up to equivalence -/
@[simps]
def prodAssoc :
    ((P * Q) * R : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}) ≃ₚ
    (P * (Q * R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}) where
  equivA := _root_.Equiv.prodAssoc P.A Q.A R.A
  equivB := fun a => {
    toFun := Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr)
    invFun := Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr)
    left_inv x := by rcases x with (_ | _) | _ <;> simp
    right_inv x := by rcases x with _ | (_ | _) <;> simp
  }

/-- Equivalence is preserved under product: if `P ≃ₚ R` and `Q ≃ₚ S`, then `P * Q ≃ₚ R * S` -/
@[simps]
def prodCongr {P Q} {R : PFunctor.{uA₃, uB₃}} {S : PFunctor.{uA₄, uB₄}}
    (e₁ : P ≃ₚ R) (e₂ : Q ≃ₚ S) : P * Q ≃ₚ (R * S : PFunctor.{max uA₃ uA₄, max uB₃ uB₄}) where
  equivA := _root_.Equiv.prodCongr e₁.equivA e₂.equivA
  equivB := fun a => {
    toFun := Sum.elim (Sum.inl ∘ e₁.equivB a.1) (Sum.inr ∘ e₂.equivB a.2)
    invFun := Sum.elim (Sum.inl ∘ (e₁.equivB a.1).symm) (Sum.inr ∘ (e₂.equivB a.2).symm)
    left_inv x := by rcases x with _ | _ <;> simp
    right_inv x := by rcases x with _ | _ <;> simp
  }

/-- Rearrangement of nested products: `(P * Q) * (R * S) ≃ₚ (P * R) * (Q * S)` -/
@[simps]
def prodProdProdComm :
    ((P * Q) * (R * S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, max uB₁ uB₂ uB₃ uB₄}) ≃ₚ
    ((P * R) * (Q * S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, max uB₁ uB₂ uB₃ uB₄}) where
  equivA := _root_.Equiv.prodProdProdComm P.A Q.A R.A S.A
  equivB := fun a => {
    toFun := Sum.elim
      (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl))
      (Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr))
    invFun := Sum.elim
      (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl))
      (Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr))
    left_inv x := by rcases x with (_ | _) | (_ | _) <;> simp
    right_inv x := by rcases x with (_ | _) | (_ | _) <;> simp
  }

/-- Product distributes over sum: `P * (Q + R) ≃ₚ (P * Q) + (P * R)` -/
@[simps]
def prodSumDistrib (R : PFunctor.{uA₃, uB₂}):
    (P * (Q + R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) ≃ₚ
    ((P * Q) + (P * R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) where
  equivA := _root_.Equiv.prodSumDistrib P.A Q.A R.A
  equivB := fun a => {
    toFun := match a with
      | ⟨a, Sum.inl b⟩ => fun x => match x with
          | Sum.inl x => Sum.inl x
          | Sum.inr x => Sum.inr x
      | ⟨a, Sum.inr b⟩ => fun x => match x with
          | Sum.inl x => Sum.inl x
          | Sum.inr x => Sum.inr x
    invFun := match a with
      | ⟨a, Sum.inl b⟩ => fun x => match x with
        | Sum.inl x => Sum.inl x
        | Sum.inr x => Sum.inr x
      | ⟨a, Sum.inr b⟩ => fun x => match x with
        | Sum.inl x => Sum.inl x
        | Sum.inr x => Sum.inr x
    left_inv x := by rcases x with _ | _ <;> simp <;> sorry
    right_inv x := by simp <;> sorry
  }

/-- Sum distributes over product: `(P + Q) * R ≃ₚ (P * R) + (Q * R)` -/
def sumProdDistrib (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₁}) (R : PFunctor.{uA₃, uB₂}) :
    ((P + Q) * R : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) ≃ₚ
    ((P * R) + (Q * R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) :=
  sorry

end Prod

section Sigma

end Sigma

section Pi

end Pi

section ULift

variable (P : PFunctor.{uA₁, uB₁})

/-- Equivalence between a polynomial functor and its universe-lifted version -/
def uliftEquiv : P ≃ₚ (P.ulift : PFunctor.{max uA₁ u, max uB₁ v}) :=
  sorry

/-- Universe lifting is idempotent up to equivalence -/
def uliftUliftEquiv : P.ulift.ulift ≃ₚ P.ulift :=
  sorry

-- TODO: find better ways to annotate universe levels

/-- Universe lifting commutes with sum -/
def uliftSumEquiv (Q : PFunctor.{uA₂, uB₁}) :
    Equiv.{max uA₁ uA₂ u, max uB₁ v, max uA₁ uA uA₂ uA', max uB₁ uB}
    (PFunctor.ulift.{_, _, u, v} (sum.{uB₁, uA₁, uA₂} P Q))
    (sum.{max uB₁ uB, max uA₁ uA, max uA₂ uA'} (P.ulift : PFunctor.{max uA₁ uA, max uB₁ uB})
      (Q.ulift : PFunctor.{max uA₂ uA', max uB₁ uB}) : PFunctor.{max uA₁ uA uA₂ uA', max uB₁ uB}) :=
  sorry

-- /-- Universe lifting commutes with product -/
-- def uliftProdEquiv (Q : PFunctor.{uA₂, uB₂}) :
--     Equiv.{max uA₁ uA₂ u, max uB₁ v, max uA₁ uA uA₂ uA', max uB₁ uB}
--     (PFunctor.ulift.{_, _, u, v} (sum.{uB₁, uA₁, uA₂} P Q))
--     (sum.{max uB₁ uB, max uA₁ uA, max uA₂ uA'} (P.ulift : PFunctor.{max uA₁ uA, max uB₁ uB})
--       (Q.ulift : PFunctor.{max uA₂ uA', max uB₁ uB}) : PFunctor.{max uA₁ uA uA₂ uA', max uB₁ uB})
--     (P * Q).ulift ≃ₚ (P.ulift * Q.ulift) :=
--   sorry

-- same for tensor product & composition

end ULift

section Tensor

variable (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (R : PFunctor.{uA₃, uB₃})
  (S : PFunctor.{uA₄, uB₄})

/-- Tensor product with the functor Y on the right -/
def tensorY : P ⊗ y ≃ₚ P :=
  sorry

/-- Tensor product with the functor Y on the left -/
def yTensor : y ⊗ P ≃ₚ P :=
  sorry

/-- Tensor product of polynomial functors is commutative up to equivalence -/
def tensorComm :
    (P ⊗ Q : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) ≃ₚ
    (Q ⊗ P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) :=
  sorry

/-- Tensor product of polynomial functors is associative up to equivalence -/
def tensorAssoc :
    ((P ⊗ Q) ⊗ R : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}) ≃ₚ
    (P ⊗ (Q ⊗ R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}) :=
  sorry

/-- If `P ≃ₚ P'` and `Q ≃ₚ Q'`, then `P ⊗ Q ≃ₚ P' ⊗ Q'` -/
def tensorCongr {P Q} {R : PFunctor.{uA₃, uB₁}} {S : PFunctor.{uA₄, uB₁}} (e₁ : P ≃ₚ R) (e₂ : Q ≃ₚ S) :
    P ⊗ Q ≃ₚ (R ⊗ S : PFunctor.{max uA₃ uA₄, uB₁}) :=
  sorry

/-- Rearrangement of nested tensor products: `(P ⊗ Q) ⊗ (R ⊗ S) ≃ₚ (P ⊗ R) ⊗ (Q ⊗ S)` -/
def tensorTensorTensorComm :
    ((P ⊗ Q) ⊗ (R ⊗ S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, max uB₁ uB₂ uB₃ uB₄}) ≃ₚ
    ((P ⊗ R) ⊗ (Q ⊗ S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, max uB₁ uB₂ uB₃ uB₄}) :=
  sorry

/-- Tensor product distributes over sum: `P ⊗ (Q + R) ≃ₚ (P ⊗ Q) + (P ⊗ R)` -/
def tensorSumDistrib (R : PFunctor.{uA₃, uB₂}):
    (P ⊗ (Q + R : PFunctor.{max uA₂ uA₃, uB₂})) ≃ₚ
    ((P ⊗ Q) + (P ⊗ R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) :=
  sorry

/-- Sum distributes over tensor product: `(P + Q) ⊗ R ≃ₚ (P ⊗ R) + (Q ⊗ R)` -/
def sumTensorDistrib (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₁}) (R : PFunctor.{uA₃, uB₂}) :
    ((P + Q : PFunctor.{max uA₁ uA₂, uB₁}) ⊗ R) ≃ₚ
    ((P ⊗ R) + (Q ⊗ R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) :=
  sorry

end Tensor

section Comp

end Comp

end Equiv

end PFunctor
