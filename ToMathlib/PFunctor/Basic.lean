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

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄ uA₅ uB₅ uA₆ uB₆ vA vB

namespace PFunctor

section Basic

/-- The zero polynomial functor, defined as `A = PEmpty` and `B _ = PEmpty`, is the identity with
  respect to sum (up to equivalence) -/
instance : Zero PFunctor.{uA, uB} where
  zero := ⟨PEmpty, fun _ => PEmpty⟩

/-- The unit polynomial functor, defined as `A = PUnit` and `B _ = PEmpty`, is the identity with
  respect to product (up to equivalence) -/
instance : One PFunctor.{uA, uB} where
  one := ⟨PUnit, fun _ => PEmpty⟩

/-- The monomial functor, also written `P(X) = A X^ B`, has `A` as its head type and the constant
  family `B_a = B` as the child type for each each shape `a : A` . -/
def monomial (A : Type uA) (B : Type uB) : PFunctor.{uA, uB} :=
  ⟨A, fun _ => B⟩

@[inherit_doc] scoped[PFunctor] infixr:80 " X^ " => monomial

/-- The constant polynomial functor `P(X) = A X^ PEmpty` -/
def C (A : Type uA) : PFunctor.{uA, uB} :=
  A X^ PEmpty

/-- The variable (or indeterminate) polynomial functor `X`, defined as `P(X) = PUnit X^ PUnit`.

This is the identity with respect to tensor product and composition (up to equivalence). -/
def X : PFunctor.{uA, uB} :=
  PUnit X^ PUnit

/-- The linear polynomial functor `P(X) = A X` -/
def linear (A : Type uA) : PFunctor.{uA, uB} :=
  A X^ PUnit

/-- The self monomial polynomial functor `P(X) = S X^ S` -/
def selfMonomial (S : Type uA) : PFunctor.{uA, uA} :=
  S X^ S

/-- The pure power polynomial functor `P(X) = X^ B` -/
def purePower (B : Type uB) : PFunctor.{uA, uB} :=
  PUnit X^ B

/-- A polynomial functor is representable if it is equivalent to `X^A` for some type `A`. -/
alias representable := purePower

instance : IsEmpty (A 0) := inferInstanceAs (IsEmpty PEmpty)
instance : Unique (A 1) := inferInstanceAs (Unique PUnit)
instance {a} : IsEmpty (B 1 a) := inferInstanceAs (IsEmpty PEmpty)
instance {α} (a : α) : IsEmpty (B (C α) a) := inferInstanceAs (IsEmpty PEmpty)
instance : Unique (A X) := inferInstanceAs (Unique PUnit)
instance {a} : Unique (B X a) := inferInstanceAs (Unique PUnit)
instance {α} (a : α) : Unique (B (linear α) a) := inferInstanceAs (Unique PUnit)
instance {β} : Unique (A (purePower β)) := inferInstanceAs (Unique PUnit)

@[simp] lemma C_empty : C PEmpty = 0 := rfl
@[simp] lemma C_unit : C PUnit = 1 := rfl

@[simp] lemma C_A (A : Type u) : (C A).A = A := rfl
@[simp] lemma C_B (A : Type u) (a : (C A).A) : (C A).B a = PEmpty := rfl

@[simp] lemma X_A : X.A = PUnit := rfl
@[simp] lemma X_B (a : X.A) : X.B a = PUnit := rfl

@[simp] lemma linear_A (A : Type u) : (linear A).A = A := rfl
@[simp] lemma linear_B (A : Type u) (a : (linear A).A) : (linear A).B a = PUnit := rfl

@[simp] lemma selfMonomial_A (S : Type u) : (selfMonomial S).A = S := rfl
@[simp] lemma selfMonomial_B (S : Type u) (a : (selfMonomial S).A) : (selfMonomial S).B a = S := rfl
@[simp] lemma selfMonomial_unit : selfMonomial PUnit = X := rfl

@[simp] lemma purePower_A (B : Type u) : (purePower B).A = PUnit := rfl
@[simp] lemma purePower_B (B : Type u) (a : (purePower B).A) : (purePower B).B a = B := rfl
@[simp] lemma purePower_unit : purePower PUnit = X := rfl

end Basic
