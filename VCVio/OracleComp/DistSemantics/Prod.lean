/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.Seq

/-!
# Lemmas About the Distribution Semantics Involving `Prod`

This file collects various lemmas about computations involving `Prod`.

NOTE: A lot of these could be implemented for more general functors/monads to mathlib
TODO: Variables
-/

open OracleSpec ENNReal BigOperators Prod

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β γ δ : Type v}

lemma probOutput_prod_mk_eq_probEvent [spec.FiniteRange] [DecidableEq α] [DecidableEq β]
    (oa : OracleComp spec (α × β)) (x : α) (y : β) :
    [= (x, y) | oa] = [λ z ↦ z.1 = x ∧ z.2 = y | oa] := by
  simp [← probEvent_eq_eq_probOutput, eq_iff_fst_eq_snd_eq]

@[simp]
lemma fst_map_prod_map (oa : OracleComp spec (α × β)) (f : α → γ) (g : β → δ) :
    fst <$> map f g <$> oa = (f ∘ Prod.fst) <$> oa := by
  simp [Functor.map_map]; rfl

@[simp]
lemma snd_map_prod_map (oa : OracleComp spec (α × β)) (f : α → γ) (g : β → δ) :
    snd <$> map f g <$> oa = (g ∘ Prod.snd) <$> oa := by
  simp [Functor.map_map]; rfl

section seq_map_mk -- TODO: bind versions of these lemmas

variable [spec.FiniteRange] (oa : OracleComp spec α) (ob : OracleComp spec β)
    (x : α) (y : β) (p : α → Prop) (q : β → Prop)

@[simp]

lemma probOutput_seq_map_prod_mk_eq_mul :
    [= (x, y) | Prod.mk <$> oa <*> ob] = [= x | oa] * [= y | ob] :=
  probOutput_seq_map_eq_mul_of_injective2 oa ob Prod.mk Prod.mk.injective2 x y

lemma probOutput_seq_map_prod_mk_eq_mul' :
    [= (x, y) | (λ x y ↦ (y, x) : β → α → α × β) <$> ob <*> oa] = [= x | oa] * [= y | ob] :=
  by rw [probOutput_seq_map_swap, probOutput_seq_map_prod_mk_eq_mul]

@[simp]
lemma probEvent_seq_map_prod_mk_eq_mul :
    [λ z ↦ p z.1 ∧ q z.2 | Prod.mk <$> oa <*> ob] = [p | oa] * [q | ob] :=
  probEvent_seq_map_eq_mul Prod.mk oa ob _ p q (λ _ _ _ _ ↦ Iff.rfl)

lemma probEvent_seq_map_prod_mk_eq_mul' :
    [λ z ↦ p z.1 ∧ q z.2 | (λ x y ↦ (y, x) : β → α → α × β) <$> ob <*> oa] = [p | oa] * [q | ob] :=
  by rw [probEvent_seq_map_swap, probEvent_seq_map_prod_mk_eq_mul]

end seq_map_mk

section mk_subsingleton

@[simp]
lemma fst_map_prod_mk_of_subsingleton [Subsingleton β]
    (oa : OracleComp spec α) (y : β) : fst <$> (·, y) <$> oa = oa := by
  simp [map_eq_bind_pure_comp, bind_assoc]

@[simp]
lemma snd_map_prod_mk_of_subsingleton [Subsingleton α]
    (ob : OracleComp spec β) (x : α) : snd <$> (x, ·) <$> ob = ob := by
  simp [Functor.map_map]

end mk_subsingleton

lemma probEvent_fst_eq_snd [spec.FiniteRange] [DecidableEq α] (oa : OracleComp spec (α × α)) :
    [λ z ↦ z.1 = z.2 | oa] = ∑' x : α, [= (x, x) | oa] := by
  rw [probEvent_eq_tsum_ite, ENNReal.tsum_prod', ENNReal.tsum_comm]
  refine tsum_congr (λ x ↦ _root_.trans (tsum_congr (λ x' ↦ ?_)) (tsum_ite_eq x [= (x, x) | oa]))
  by_cases hx : x' = x <;> simp [hx]

end OracleComp
