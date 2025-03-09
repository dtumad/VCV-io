/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist
import ToMathlib.General

/-!
# Lemmas About the Distribution Semantics of Failure Operations

This file collects various lemmas about the operations associated to `Alternative`,
like `guard`, `orElse`, `tryM?`, etc.
-/

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type v}

protected lemma orElse_def {ι : Type u} {spec : OracleSpec ι} {α : Type u}
    (oa oa' : OracleComp spec α) : (oa <|> oa') = OptionT.mk
      (do match ← OptionT.run oa with | some a => pure (some a) | _  => OptionT.run oa') := rfl

@[simp]
lemma probFailure_orElse {ι : Type u} {spec : OracleSpec ι} {α : Type u} [h : spec.FiniteRange]
    (oa oa' : OracleComp spec α) : [⊥ | oa <|> oa'] = [⊥ | oa] * [⊥ | oa'] := by
  rw [OracleComp.orElse_def]
  sorry

@[simp]
lemma support_orElse {ι : Type u} {spec : OracleSpec ι} {α : Type u}
    (oa oa' : OracleComp spec α) [Decidable oa.noFailure] : (oa <|> oa').support =
      if oa.noFailure then oa.support else oa.support ∪ oa'.support := by
  sorry

end OracleComp
