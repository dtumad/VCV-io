/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Monad

/-!
# Probability Distributions of Boolean/Propositional Computations
-/


lemma probOutput_true_eq_probEvent {α} {m : Type → Type u} [Monad m] [HasEvalDist m]
    (mx : m α) (p : α → Prop) : Pr{let x ← mx}[p x] = Pr[p | mx] := by
  rw [probEvent_eq_tsum_indicator]
  rw [probOutput_bind_eq_tsum]
  refine tsum_congr fun α => ?_
  simp [Set.indicator]
  congr
  rw [eq_true_eq_id]
  rfl
