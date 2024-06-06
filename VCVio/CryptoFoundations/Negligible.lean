/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp

/-!
# Negligible Functions
-/

open ENNReal

-- TODO: fix
def negligible (f : ℕ → ℝ≥0∞) : Prop := f ≠ λ _ ↦ ∞
