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
-/

open OracleSpec ENNReal BigOperators Prod

namespace OracleComp

variable {spec : OracleSpec} {α β : Type}

@[simp]
lemma probOutput_prod_mk (oa : OracleComp spec (α × β)) (x : α) :
    [= (x, y) | oa] = [λ z ↦ z.1 = x ∧ z.2 = y | oa] := by
  simp [← probEvent_eq_eq_probOutput, eq_iff_fst_eq_snd_eq]

section map

@[simp]
lemma fst_map_prod_map (oa : OracleComp spec (α × β)) (f : α → γ) (g : β → δ) :
    fst <$> map f g <$> oa = (λ x ↦ f x.1) <$> oa := by
  simp only [Functor.map_map, Function.comp, Prod_map]

@[simp]
lemma snd_map_prod_map (oa : OracleComp spec (α × β)) (f : α → γ) (g : β → δ) :
    snd <$> map f g <$> oa = (λ x ↦ g x.2) <$> oa := by
  simp only [Functor.map_map, Function.comp, Prod_map]

end map

section mk_subsingleton

@[simp]
lemma fst_map_prod_mk_of_subsingleton [Subsingleton β]
    (oa : OracleComp spec α) (y : β) : fst <$> (·, y) <$> oa = oa := by
  simp only [Functor.map_map, Function.comp, id_map']

@[simp]
lemma snd_map_prod_mk_of_subsingleton [Subsingleton α]
    (ob : OracleComp spec β) (x : α) : snd <$> (x, ·) <$> ob = ob := by
  simp only [Functor.map_map, snd_comp_mk, id_map]

end mk_subsingleton

lemma probEvent_fst_eq_snd [DecidableEq α] (oa : OracleComp spec (α × α)) :
    [λ z ↦ z.1 = z.2 | oa] = ∑' x : α, [= (x, x) | oa] := by
  rw [probEvent_eq_tsum_ite, ENNReal.tsum_prod', ENNReal.tsum_comm]
  refine tsum_congr (λ x ↦ _root_.trans (tsum_congr (λ x' ↦ ?_)) (tsum_ite_eq x [= (x, x) | oa]))
  by_cases hx : x' = x <;> simp [hx]

end OracleComp
