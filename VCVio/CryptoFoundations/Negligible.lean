/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import ToMathlib.General

/-!
# Negligible Functions
-/

open ENNReal Asymptotics Filter

-- TODO: fix
def negligible (f : ℕ → ℝ≥0∞) : Prop :=
SuperpolynomialDecay atTop (λ x ↦ ↑x) f

lemma negligible_zero : negligible 0 := superpolynomialDecay_zero _ _

lemma negligible_of_zero {f : ℕ → ℝ≥0∞} (hf : ∀ n, f n = 0) : negligible f := by
  convert negligible_zero
  refine funext hf
