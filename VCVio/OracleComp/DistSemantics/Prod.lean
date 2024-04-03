/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.Seq

/-!
# Lemmas About the Distribution Semantics Involving `Prod`

This file collects various lemmas about computations involving `Prod`.
-/

open OracleSpec ENNReal BigOperators Prod

namespace OracleComp

variable {spec : OracleSpec} {α β : Type}

@[simp]
lemma fst_map_prod_map (oa : OracleComp spec (α × β)) (f : α → γ) (g : β → δ) :
    fst <$> map f g <$> oa = (λ x ↦ f x.1) <$> oa := by
  simp [Functor.map_map, Function.comp]

@[simp]
lemma snd_map_prod_map (oa : OracleComp spec (α × β)) (f : α → γ) (g : β → δ) :
    snd <$> map f g <$> oa = (λ x ↦ g x.2) <$> oa := by
  simp [Functor.map_map, Function.comp]

end OracleComp
