/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Probability.CDF

/-!
# Negligible Functions

This file defines a simple wrapper around `SuperpolynomialDecay` for function from `ℕ → ℝ≥0∞`,
as this is usually the situation for cryptographic reductions.

Adding a general API might be useful, but usually unfolding to `SuperpolynomialDecay` is fine.
-/

open ENNReal Asymptotics Filter

/-- A function `f` is negligible if it decays faster than any polynomial function. -/
def negligible (f : ℕ → ℝ≥0∞) : Prop :=
  SuperpolynomialDecay atTop (λ x ↦ ↑x) f

@[simp] def negligible_iff (f : ℕ → ℝ≥0∞) :
    negligible f ↔ SuperpolynomialDecay atTop (λ x ↦ ↑x) f := Iff.rfl

lemma negligible_zero : negligible 0 := superpolynomialDecay_zero _ _

lemma negligible_of_zero {f : ℕ → ℝ≥0∞} (hf : ∀ n, f n = 0) : negligible f :=
  have : f = 0 := funext hf; this ▸ negligible_zero
