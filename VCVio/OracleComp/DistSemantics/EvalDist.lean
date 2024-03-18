/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.Support
import ToMathlib.General
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open ENNReal BigOperators

namespace OracleComp

variable {spec : OracleSpec} {α β : Type}

noncomputable def evalDist : {α : Type} → OracleComp spec α → PMF α
| _, pure' α a => PMF.pure a
| _, query_bind' i _ α oa => PMF.bind (PMF.ofFintype (λ _ ↦ (Fintype.card (spec.range i))⁻¹)
    (Fintype.sum_inv_card (spec.range i))) (λ a ↦ evalDist $ oa a)

noncomputable def probOutput (oa : OracleComp spec α) (x : α) : ℝ≥0∞ :=
evalDist oa x

noncomputable def probEvent (oa : OracleComp spec α) (p : α → Prop) : ℝ≥0∞ :=
(evalDist oa).toOuterMeasure p

notation "[=" x "|" oa "]" => probOutput oa x
notation "[" p "|" oa "]" => probEvent oa p

lemma probOutput.def (oa : OracleComp spec α) (x : α) : [= x | oa] = evalDist oa x := rfl
lemma probEvent.def (oa : OracleComp spec α) (p : α → Prop) :
  [p | oa] = (evalDist oa).toOuterMeasure p := rfl

noncomputable example : ℝ≥0∞ := [= 5 | do let x ←$[0..4]; return x + 1]
noncomputable example : ℝ≥0∞ := [(. + 1 = 5) | do let x ←$[0..4]; return x]

lemma evalDist_pure' (x : α) : evalDist (pure' α x : OracleComp spec α) = PMF.pure x := rfl

lemma evalDist_query_bind' (i : spec.ι) (t : spec.domain i)
  (oa : spec.range i → OracleComp spec α) : evalDist (query_bind' i t α oa) =
  PMF.bind (PMF.ofFintype (λ _ ↦ (Fintype.card (spec.range i))⁻¹)
    (Fintype.sum_inv_card (spec.range i))) (λ a ↦ evalDist $ oa a) := rfl

section support

lemma mem_support_evalDist_iff (oa : OracleComp spec α) (x : α) :
  x ∈ (evalDist oa).support ↔ x ∈ oa.support :=
by induction oa using OracleComp.inductionOn with
| h_pure x => simp_rw [← OracleComp.pure'_eq_pure, evalDist_pure', PMF.support_pure, support_pure']
| h_query_bind i t oa hoa => simp_rw [← query_bind'_eq_query_bind, evalDist_query_bind',
    PMF.support_bind, support_query_bind', PMF.support_ofFintype, Set.mem_iUnion, hoa,
    Function.mem_support, ne_eq, ENNReal.inv_eq_zero, nat_ne_top, not_false_eq_true, exists_const]

-- lemma mem_support_evalDist_iff' [DecidableEq α] (oa : OracleComp spec α) (x : α) :
--   x ∈ (evalDist oa).support ↔ x ∈ oa.finSupport :=
-- by induction oa using OracleComp.inductionOn with
-- | h_pure x => simpa only [← OracleComp.pure'_eq_pure, evalDist_pure', PMF.support_pure, finSupport]
-- | h_query_bind i t oa hoa => simp_rw [← query_bind'_eq_query_bind, evalDist_query_bind',
--     PMF.support_bind, finSupport_query_bind', PMF.support_ofFintype, Set.mem_iUnion, hoa,
--     Function.mem_support, ne_eq, ENNReal.inv_eq_zero, nat_ne_top, not_false_eq_true, exists_const]

@[simp] lemma support_evalDist (oa : OracleComp spec α) : (evalDist oa).support = oa.support :=
Set.ext (mem_support_evalDist_iff oa)

end support

section pure

variable (x : α)

@[simp] lemma evalDist_pure : evalDist (return x : OracleComp spec α) = PMF.pure x := rfl

@[simp] lemma probOutput_pure [DecidableEq α] (y : α) :
  [= y | (return x : OracleComp spec α)] = if y = x then 1 else 0 := by
  split_ifs with h
  · induction h
    exact PMF.pure_apply_self y
  · exact PMF.pure_apply_of_ne _ _ h

@[simp] lemma probEvent_pure (p : α → Prop) [DecidablePred p] :
  [p | (return x : OracleComp spec α)] = if p x then 1 else 0 :=
(PMF.toOuterMeasure_pure_apply x p).trans (by congr)

end pure

section bind

variable (oa : OracleComp spec α) (ob : α → OracleComp spec β)

@[simp] lemma evalDist_bind : evalDist (oa >>= ob) = (evalDist oa).bind (evalDist ∘ ob) :=
by induction oa using OracleComp.inductionOn with
| h_pure _ => simp only [pure_bind, evalDist_pure, PMF.pure_bind, Function.comp_apply]
| h_query_bind _ _ _ hoa => simp [bind_assoc, ← query_bind'_eq_query_bind, evalDist, hoa]

@[simp] lemma probOutput_bind_eq_tsum (y : β) :
  [= y | oa >>= ob] = ∑' x : α, [= x | oa] * [= y | ob x] :=
by simp only [probOutput.def, evalDist_bind, PMF.bind_apply, Function.comp_apply]

@[simp] lemma probOutput_bind_eq_sum [Fintype α] :
  [= y | oa >>= ob] = ∑ x : α, [= x | oa] * [= y | ob x] :=
(probOutput_bind_eq_tsum oa ob y).trans (tsum_eq_sum (λ _ h ↦ False.elim (h (Finset.mem_univ _))))

@[simp] lemma probOutput_bind_eq_sum_finSupport [DecidableEq α] :
  [= y | oa >>= ob] = ∑ x in oa.finSupport, [= x | oa] * [= y | ob x] :=
(probOutput_bind_eq_tsum oa ob y).trans (tsum_eq_sum (λ x hx ↦
  mul_eq_zero_of_left (sorry) _))

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

end OracleComp
