/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Probability.CDF

/-!
# Negligible Functions

This file defines a simple wrapper around `SuperpolynomialDecay` for function from `ℕ → ℝ`,
as this is usually the situation for cryptographic reductions.

Adding a general API might be useful, but usually unfolding to `SuperpolynomialDecay` is fine.
-/

open ENNReal NNReal Asymptotics Filter

/-- A function `f` is `Negligible` if it decays faster than any polynomial function. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  SuperpolynomialDecay atTop (fun x => ↑x) f

def Negligible_def (f : ℕ → ℝ) :
    Negligible f ↔ SuperpolynomialDecay atTop (fun x => ↑x) f := Iff.rfl

lemma Negligible_zero : Negligible 0 := superpolynomialDecay_zero _ _

lemma Negligible_of_zero {f : ℕ → ℝ} (hf : ∀ n, f n = 0) : Negligible f :=
  have : f = 0 := funext hf; this ▸ Negligible_zero

lemma Negligible.mul (f g : ℕ → ℝ) (hf : Negligible f) (hg : Negligible g) :
    Negligible (f * g) := SuperpolynomialDecay.mul hf hg

lemma Negligible_iff_isBigO (f : ℕ → ℝ) :
    Negligible f ↔ ∀ z : ℤ, f =O[atTop] (fun x => (x : ℝ) ^ z) := by
  rw [Negligible_def, superpolynomialDecay_iff_isBigO]
  exact tendsto_natCast_atTop_atTop
