/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist

/-!
# Computations that Never Fail

This file defines a class `OracleComp.NoFailure` for computations that never fail regardless
of the behavior of oracles. This can be useful for simplifying some probability calculations.
-/

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type u}

class noFailure {α : Type u} (oa : OracleComp spec α) : Prop where
  no_failure : by induction oa using OracleComp.construct with
    | pure _ => exact True
    | failure => exact False
    | query_bind _ _ r => exact ∀ x, r x

instance noFailure_pure (x : α) : noFailure (pure x : OracleComp spec α) where
  no_failure := True.intro

instance noFailure_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    [h : noFailure oa] [h' : ∀ x, noFailure (ob x)] : noFailure (oa >>= ob) where
  no_failure := by
    induction oa using OracleComp.inductionOn generalizing h with
    | pure x => exact (h' x).no_failure
    | failure => exact h.no_failure.elim
    | query_bind _ _ r => sorry

end OracleComp
