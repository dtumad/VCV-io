/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Data.Fintype.Card

structure OracleSpec where
  ι : Type
  domain : ι → Type
  range : ι → Type
  ι_decidableEq : DecidableEq ι
  domain_decidableEq : ∀ i, DecidableEq $ domain i
  range_decidableEq : ∀ i, DecidableEq $ range i
  range_inhabited : ∀ i, Inhabited $ range i
  range_fintype : ∀ i, Fintype $ range i

namespace OracleSpec

instance ι.decidableEq' (spec : OracleSpec) :
  DecidableEq spec.ι := spec.ι_decidableEq

instance domain.decidableEq' {spec : OracleSpec} (i : spec.ι) :
  DecidableEq (spec.domain i) := spec.domain_decidableEq i

instance range.decidableEq' {spec : OracleSpec} (i : spec.ι) :
  DecidableEq (spec.range i) := spec.range_decidableEq i

instance range.inhabited {spec : OracleSpec} (i : spec.ι) :
  Inhabited (spec.range i) := spec.range_inhabited i

instance range.fintype' {spec : OracleSpec} (i : spec.ι) :
  Fintype (spec.range i) := spec.range_fintype i

@[simp] lemma card_range_ne_zero {spec : OracleSpec} (i : spec.ι) :
  Fintype.card (spec.range i) ≠ 0 := Fintype.card_ne_zero

@[simps] def emptySpec : OracleSpec :=
{ ι := Empty,
  domain := λ _ ↦ Unit,
  range := λ _ ↦ Unit,
  range_inhabited := inferInstance,
  ι_decidableEq := inferInstance,
  domain_decidableEq := inferInstance,
  range_decidableEq := inferInstance,
  range_fintype := inferInstance }

instance (i : emptySpec.ι) : Unique (emptySpec.domain i) := PUnit.unique
instance (i : emptySpec.ι) : Unique (emptySpec.range i) := PUnit.unique

instance : EmptyCollection OracleSpec := ⟨emptySpec⟩
instance : Inhabited OracleSpec := ⟨∅⟩

@[simps] def singletonSpec (T U : Type) [Inhabited U] [DecidableEq T]
  [DecidableEq U] [Fintype U] : OracleSpec :=
{ ι := Unit,
  domain := λ _ ↦ T,
  range := λ _ ↦ U,
  range_inhabited := inferInstance,
  ι_decidableEq := inferInstance,
  domain_decidableEq := inferInstance,
  range_decidableEq := inferInstance,
  range_fintype := inferInstance }

infixl : 25 " →ₒ " => singletonSpec

instance singletonSpec_ι_unique (T U : Type) [Inhabited U] [DecidableEq T]
  [DecidableEq U] [Fintype U] : Unique (T →ₒ U).ι := PUnit.unique

instance : Append OracleSpec :=
{ append := λ spec spec' ↦
  { ι := spec.ι ⊕ spec'.ι,
    domain := Sum.elim spec.domain spec'.domain,
    range := Sum.elim spec.range spec'.range,
    range_inhabited := λ i ↦ Sum.recOn i spec.range_inhabited spec'.range_inhabited,
    ι_decidableEq := inferInstance,
    domain_decidableEq := λ i ↦ Sum.recOn i spec.domain_decidableEq spec'.domain_decidableEq,
    range_decidableEq := λ i ↦ Sum.recOn i spec.range_decidableEq spec'.range_decidableEq,
    range_fintype := λ i ↦ Sum.recOn i spec.range_fintype spec'.range_fintype } }

@[simp] lemma domain_append_inl (spec spec' : OracleSpec) (i : spec.ι) :
  (spec ++ spec').domain (Sum.inl i) = spec.domain i := rfl
@[simp] lemma domain_append_inr (spec spec' : OracleSpec) (i : spec'.ι) :
  (spec ++ spec').domain (Sum.inr i) = spec'.domain i := rfl
@[simp] lemma range_append_inl (spec spec' : OracleSpec) (i : spec.ι) :
  (spec ++ spec').range (Sum.inl i) = spec.range i := rfl
@[simp] lemma range_append_inr (spec spec' : OracleSpec) (i : spec'.ι) :
  (spec ++ spec').range (Sum.inr i) = spec'.range i := rfl

def coinSpec : OracleSpec := Unit →ₒ Bool

@[simp] lemma card_range_coinSpec (i : Unit) :
  Fintype.card (coinSpec.range i) = 2 := rfl

@[simps] def unifSpec : OracleSpec :=
{ ι := ℕ,
  domain := λ _ ↦ Unit,
  range := λ n ↦ Fin (n + 1),
  range_inhabited := inferInstance,
  ι_decidableEq := inferInstance,
  domain_decidableEq := inferInstance,
  range_decidableEq := inferInstance,
  range_fintype := inferInstance }

@[simp] lemma card_range_unifSpec (n : ℕ) :
  Fintype.card (unifSpec.range n) = n + 1 := Finset.card_fin (n + 1)

end OracleSpec
