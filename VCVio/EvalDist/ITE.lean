/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, František Silváši
-/
import VCVio.EvalDist.Basic

/-!
# Denotational Semantics for ITE and Guard Operations
-/

section ite

-- Pushing into `ite` is more natural than usual in our setting, so we make it `simp`.
-- This comes up a lot in our applications with both cases and `guard` statements.

@[simp] lemma evalDist_ite (p : Prop) [Decidable p] (mx mx' : m α) :
    evalDist (if p then mx else mx') = if p then evalDist mx else evalDist mx' := by
  by_cases hp : p <;> simp [hp]

end ite

section guard


end guard
