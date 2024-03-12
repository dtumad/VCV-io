/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import «VCV-io».OracleComp.DistSemantics.Support
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace OracleComp

open ENNReal

variable {spec : OracleSpec} {α β : Type}

noncomputable def evalDist : {α : Type} → OracleComp spec α → PMF α
| _, pure' α a => PMF.pure a
| _, query_bind' i t α oa =>
    let unifQueryPMF := (PMF.ofFintype (λ _ ↦ 1 / Fintype.card (spec.range i)) (by
      simp only [Finset.card_univ, one_div, Finset.sum_const, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by simp) (nat_ne_top _)))
    PMF.bind unifQueryPMF (λ a ↦ evalDist $ oa a)

noncomputable def probOutput (oa : OracleComp spec α) (x : α) : ℝ≥0∞ :=
evalDist oa x

noncomputable def probEvent (oa : OracleComp spec α) (p : α → Prop) : ℝ≥0∞ :=
(evalDist oa).toOuterMeasure p

section pure

--
end pure

section bind

--
end bind

section query

--
end query

section map

--
end map

section seq

--
end seq

section ite

--
end ite

section coin

--
end coin

section uniformFin

--
end uniformFin

notation "[=" x "|" oa "]" => probOutput oa x
notation "[" p "|" oa "]" => probEvent oa p

noncomputable example : ℝ≥0∞ := [= 5 | do let x ←$[0..4]; return x + 1]
noncomputable example : ℝ≥0∞ := [(. + 1 = 5) | do let x ←$[0..4]; return x]

end OracleComp
