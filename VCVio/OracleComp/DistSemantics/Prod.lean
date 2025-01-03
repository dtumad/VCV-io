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

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β γ δ : Type}

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

section seq_map_mk

variable (oa : OracleComp spec α) (ob : OracleComp spec β)
    (x : α) (y : β)

@[simp]
lemma probOutput_seq_map_prod_mk_eq_mul [spec.FiniteRange] :
    [= (x, y) | (·, ·) <$> oa <*> ob] = [= x | oa] * [= y | ob] :=
  probOutput_seq_map_eq_mul_of_injective2 oa ob Prod.mk Prod.mk.injective2 x y

@[simp]
lemma probOutput_seq_map_prod_mk_eq_mul' [spec.FiniteRange] :
    [= (x, y) | (λ x y ↦ (y, x)) <$> ob <*> oa] = [= x | oa] * [= y | ob] :=
  (probOutput_seq_map_swap oa ob (·, ·) (x, y)).trans
    (probOutput_seq_map_prod_mk_eq_mul oa ob x y)

@[simp]
lemma probOutput_seq_map_prod_mk_eq_mul'' [spec.FiniteRange] :
    [= (x, y) | Prod.mk <$> oa <*> ob] = [= x | oa] * [= y | ob] :=
  probOutput_seq_map_eq_mul_of_injective2 oa ob Prod.mk Prod.mk.injective2 x y


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
