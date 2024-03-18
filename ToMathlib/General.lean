/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Instances.ENNReal

/-!
# Lemmas to be Ported to Mathlib

This file gives a centralized location to add lemmas that belong better
in general mathlib than in the project itself.
-/

open ENNReal

lemma Fintype.sum_inv_card (α : Type) [Fintype α] [Nonempty α] :
  Finset.sum Finset.univ (λ _ ↦ (Fintype.card α)⁻¹ : α → ℝ≥0∞) = 1 := by
  simp only [Finset.card_univ, one_div, Finset.sum_const, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by simp) (nat_ne_top _)
