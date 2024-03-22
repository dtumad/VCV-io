/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.Support
import ToMathlib.General
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Denotational Semantics for Output Distributions

This file gives definitions for the output distribution or computations with uniform oracles.
Given a computation `oa : OracleComp spec α` we define a distribution `evalDist oa : PMF α`
expressing the probability of getting an output `x : α` if the oracles in `spec` were to
respond uniformly to all queries.

We also define functions `probOutput oa x` and `probEvent oa p` for the probabilities of a
specific output of of a specific predicate holding on the output respectively.
We introduce notation `[= x | oa]` and `[p | oa]` for these defintions as well.

The behavior of more complex oracles should first be implemented using `OracleComp.simulate`
before applying these constructions.

These definitons are compatible with `OracleComp.support` and `OracleComp.finSupport` in the sense
that values are in the support iff they have non-zero probability under `evalDist`.

We give many simp lemmas involving `tsum` a lower priority, as otherwise the simplifier will
always choose them over versions involving `sum` (as they require `DecidableEq` or `Fintype`)

TODO: We define `distEquiv` on it's own somewhere else
-/

namespace OracleComp

open ENNReal BigOperators

variable {spec : OracleSpec} {α β : Type}

/-- Associate a probability mass function to a computation, where the probability is the odds of
getting a given output assuming all oracles responded uniformly at random. -/
noncomputable def evalDist : {α : Type} → OracleComp spec α → PMF α
| _, pure' α a => PMF.pure a
| _, query_bind' i _ α oa => PMF.bind (PMF.ofFintype (λ _ ↦ (Fintype.card (spec.range i))⁻¹)
    (Fintype.sum_inv_card (spec.range i))) (λ a ↦ evalDist $ oa a)

lemma evalDist_pure' (x : α) : evalDist (pure' α x : OracleComp spec α) = PMF.pure x := rfl

lemma evalDist_query_bind' (i : spec.ι) (t : spec.domain i)
    (oa : spec.range i → OracleComp spec α) : evalDist (query_bind' i t α oa) =
  PMF.bind (PMF.ofFintype (λ _ ↦ (Fintype.card (spec.range i))⁻¹)
    (Fintype.sum_inv_card (spec.range i))) (λ a ↦ evalDist $ oa a) := rfl

/-- `[= x | oa]` is the probability of getting the given output `x` from the computation `oa`,
assuming all oracles respond uniformly at random. -/
noncomputable def probOutput (oa : OracleComp spec α) (x : α) : ℝ≥0∞ :=
evalDist oa x

/-- `[p | oa]` is the probability of getting a result that satisfies a predicate `p`
after running the computation `oa`, assuming all oracles respond uniformly at random.-/
noncomputable def probEvent (oa : OracleComp spec α) (p : α → Prop) : ℝ≥0∞ :=
(evalDist oa).toOuterMeasure p

notation "[=" x "|" oa "]" => probOutput oa x
notation "[" p "|" oa "]" => probEvent oa p

lemma probOutput.def (oa : OracleComp spec α) : probOutput oa = ⇑(evalDist oa) := rfl
lemma probEvent.def (oa : OracleComp spec α) : probEvent oa = ⇑(evalDist oa).toOuterMeasure := rfl

noncomputable example : ℝ≥0∞ := [= 5 | do let x ← $[0..4]; return x + 1] -- = 1/4
noncomputable example : ℝ≥0∞ := [(. + 1 = 5) | do let x ← $[0..4]; return x] -- = 1/4

section bounds

variable {oa : OracleComp spec α} {x : α} {p : α → Prop}

@[simp] lemma probOutput_le_one : [= x | oa] ≤ 1 := PMF.coe_le_one (evalDist oa) x
@[simp] lemma probEvent_le_one : [p | oa] ≤ 1 := by
  rw [probEvent.def, PMF.toOuterMeasure_apply]
  refine le_of_le_of_eq (tsum_le_tsum ?_ ENNReal.summable ENNReal.summable) (evalDist oa).tsum_coe
  simp [Set.indicator]; intros; split_ifs <;> simp

@[simp] lemma probOutput_ne_top : [= x | oa] ≠ ∞ := PMF.apply_ne_top (evalDist oa) x
@[simp] lemma probOutput_lt_top : [= x | oa] < ∞ := PMF.apply_lt_top (evalDist oa) x
@[simp] lemma probEvent_ne_top : [p | oa] ≠ ∞ := ne_top_of_le_ne_top one_ne_top probEvent_le_one
@[simp] lemma probEvent_lt_top : [p | oa] < ∞ := lt_top_iff_ne_top.2 probEvent_ne_top

end bounds

section support

lemma mem_support_evalDist_iff (oa : OracleComp spec α) (x : α) :
    x ∈ (evalDist oa).support ↔ x ∈ oa.support := by
  induction oa using OracleComp.inductionOn with
  | h_pure => simp_rw [← OracleComp.pure'_eq_pure, evalDist_pure', PMF.support_pure, support_pure']
  | h_query_bind i t oa hoa => simp_rw [← query_bind'_eq_query_bind, evalDist_query_bind',
      PMF.support_bind, support_query_bind', PMF.support_ofFintype, Set.mem_iUnion, hoa,
      Function.mem_support, ne_eq, ENNReal.inv_eq_zero, nat_ne_top, not_false_iff, exists_const]

/-- The support of `evalDist oa` is exactly `support oa`. -/
@[simp] lemma support_evalDist (oa : OracleComp spec α) : (evalDist oa).support = oa.support :=
  Set.ext (mem_support_evalDist_iff oa)

lemma mem_support_evalDist_iff' [DecidableEq α] (oa : OracleComp spec α) (x : α) :
    x ∈ (evalDist oa).support ↔ x ∈ oa.finSupport := by
  rw [mem_support_evalDist_iff, mem_finSupport_iff_mem_support]

lemma support_evalDist' [DecidableEq α] (oa : OracleComp spec α) :
    (evalDist oa).support = ↑oa.finSupport := by
  rw [support_evalDist, coe_finSupport]

variable (oa : OracleComp spec α) (x : α) (p q : α → Prop)

@[simp low]
lemma probOutput_eq_zero_iff : [= x | oa] = 0 ↔ x ∉ oa.support := by
  rw [probOutput, PMF.apply_eq_zero_iff, support_evalDist]
@[simp]
lemma probOutput_eq_zero_iff' [DecidableEq α] : [= x | oa] = 0 ↔ x ∉ oa.finSupport := by
  rw [mem_finSupport_iff_mem_support, probOutput_eq_zero_iff]
@[simp low]
lemma probEvent_eq_zero_iff : [p | oa] = 0 ↔ ∀ x ∈ oa.support, ¬ p x := by
  simp [probEvent.def, PMF.toOuterMeasure_apply_eq_zero_iff,
    Set.disjoint_iff, ← Set.subset_empty_iff, Set.subset_def]; rfl
@[simp]
lemma probEvent_eq_zero_iff' [DecidableEq α] : [p | oa] = 0 ↔ ∀ x ∈ oa.finSupport, ¬ p x := by
  simp only [probEvent_eq_zero_iff, mem_finSupport_iff_mem_support]

@[simp low]
lemma probOutput_pos_iff : 0 < [= x | oa] ↔ x ∈ oa.support := by
  rw [pos_iff_ne_zero, ne_eq, probOutput_eq_zero_iff, not_not]
@[simp]
lemma probOutput_pos_iff' [DecidableEq α] : 0 < [= x | oa] ↔ x ∈ oa.finSupport := by
  rw [probOutput_pos_iff, mem_finSupport_iff_mem_support]
@[simp low]
lemma probEvent_pos_iff : 0 < [p | oa] ↔ ∃ x ∈ oa.support, p x := by
  simp_rw [pos_iff_ne_zero, ne_eq, probEvent_eq_zero_iff, not_forall, not_not, exists_prop]
@[simp]
lemma probEvent_pos_iff' [DecidableEq α] : 0 < [p | oa] ↔ ∃ x ∈ oa.finSupport, p x := by
  simp_rw [pos_iff_ne_zero, ne_eq, probEvent_eq_zero_iff', not_forall, not_not, exists_prop]

@[simp low]
lemma probOutput_eq_one_iff : [= x | oa] = 1 ↔ oa.support ⊆ {x} := by
  rw [probOutput.def, PMF.apply_eq_one_iff, support_evalDist, support_eq_singleton_iff]
@[simp]
lemma probOutput_eq_one_iff' [DecidableEq α] : [= x | oa] = 1 ↔ oa.finSupport ⊆ {x} := by
  rw [probOutput.def, PMF.apply_eq_one_iff, support_evalDist, support_eq_singleton_iff,
    finSupport_subset_iff_support_subset_coe, Finset.coe_singleton]
@[simp low]
lemma probEvent_eq_one_iff : [p | oa] = 1 ↔ ∀ x ∈ oa.support, p x := by
  simp [probEvent.def, PMF.toOuterMeasure_apply_eq_one_iff, Set.subset_def,
    support_evalDist, Set.mem_def]
@[simp]
lemma probEvent_eq_one_iff' [DecidableEq α] : [p | oa] = 1 ↔ ∀ x ∈ oa.finSupport, p x := by
  simp_rw [probEvent_eq_one_iff, mem_finSupport_iff_mem_support]

variable {oa x p q}

lemma probOutput_eq_zero (hx : x ∉ oa.support) :
    [= x | oa] = 0 := (probOutput_eq_zero_iff oa x).2 hx
lemma probOutput_eq_zero' [DecidableEq α] (hx : x ∉ oa.finSupport) :
    [= x | oa] = 0 := (probOutput_eq_zero_iff' oa x).2 hx
lemma probEvent_eq_zero (h : ∀ x ∈ oa.support, ¬ p x) :
    [p | oa] = 0 := (probEvent_eq_zero_iff oa p).2 h
lemma probEvent_eq_zero' [DecidableEq α] (h : ∀ x ∈ oa.finSupport, ¬ p x) :
    [p | oa] = 0 := (probEvent_eq_zero_iff' oa p).2 h

lemma probOutput_pos (hx : x ∈ oa.support) :
    0 < [= x | oa] := (probOutput_pos_iff oa x).2 hx
lemma probOutput_pos' [DecidableEq α] (hx : x ∈ oa.finSupport) :
    0 < [= x | oa] := (probOutput_pos_iff' oa x).2 hx
lemma probEvent_pos (h : ∃ x ∈ oa.support, p x) :
    0 < [p | oa] := (probEvent_pos_iff oa p).2 h
lemma probEvent_pos' [DecidableEq α] (h : ∃ x ∈ oa.finSupport, p x) :
    0 < [p | oa] := (probEvent_pos_iff' oa p).2 h

lemma probOutput_eq_one (hx : oa.support ⊆ {x}) :
    [= x | oa] = 1 := (probOutput_eq_one_iff oa x).2 hx
lemma probOutput_eq_one' [DecidableEq α] (hx : oa.finSupport ⊆ {x}) :
    [= x | oa] = 1 := (probOutput_eq_one_iff' oa x).2 hx
lemma probEvent_eq_one (h : ∀ x ∈ oa.support, p x) :
    [p | oa] = 1 := (probEvent_eq_one_iff oa p).2 h
lemma probEvent_eq_one' [DecidableEq α] (h : ∀ x ∈ oa.finSupport, p x) :
    [p | oa] = 1 := (probEvent_eq_one_iff' oa p).2 h

lemma probEvent_mono (h : ∀ x ∈ oa.support, p x → q x) : [p | oa] ≤ [q | oa] :=
  PMF.toOuterMeasure_mono _ (λ x hx ↦ h x ((oa.mem_support_evalDist_iff x).1 hx.2) hx.1)
lemma probEvent_mono' [DecidableEq α] (h : ∀ x ∈ oa.finSupport, p x → q x) : [p | oa] ≤ [q | oa] :=
  PMF.toOuterMeasure_mono _ (λ x hx ↦ h x ((oa.mem_support_evalDist_iff' x).1 hx.2) hx.1)

lemma probEvent_ext (h : ∀ x ∈ oa.support, p x ↔ q x) : [p | oa] = [q | oa] :=
  le_antisymm (probEvent_mono <| λ x hx hp ↦ (h x hx).1 hp)
    (probEvent_mono <| λ x hx hp ↦ (h x hx).2 hp)
lemma probEvent_ext' [DecidableEq α] (h : ∀ x ∈ oa.finSupport, p x ↔ q x) : [p | oa] = [q | oa] :=
  le_antisymm (probEvent_mono' <| λ x hx hp ↦ (h x hx).1 hp)
    (probEvent_mono' <| λ x hx hp ↦ (h x hx).2 hp)

@[simp]
lemma function_support_probOutput : Function.support ([= . | oa]) = oa.support := by
  simp only [Function.support, ne_eq, probOutput_eq_zero_iff, not_not, Set.setOf_mem_eq]

@[simp]
lemma function_support_probEvent : Function.support ([. | oa]) = {p | ∃ x ∈ oa.support, p x} := by
  simp only [Function.support, ne_eq, probEvent_eq_zero_iff, not_forall, not_not, exists_prop]

end support

@[simp] lemma probEvent_eq_eq_probOutput (oa : OracleComp spec α) : [(. = x) | oa] = [= x | oa] :=
  PMF.toOuterMeasure_apply_singleton (evalDist oa) x
@[simp] lemma probEvent_eq_eq_probOutput' (oa : OracleComp spec α) : [(x = .) | oa] = [= x | oa] :=
  (probEvent_ext (λ _ _ ↦ eq_comm)).trans (probEvent_eq_eq_probOutput oa)

section sums

variable (oa : OracleComp spec α) (p : α → Prop)

@[simp] lemma tsum_probOutput : ∑' x : α, [= x | oa] = 1 := (evalDist oa).tsum_coe
@[simp] lemma sum_probOutput [Fintype α] : ∑ x : α, [= x | oa] = 1 :=
  symm (oa.tsum_probOutput.symm.trans <| tsum_eq_sum' <| by simp)

/-- The probability of an event written as a sum over the set `{x | p x}` viewed as a subtype.
This notably doesn't require decidability of the predicate `p` unlike many other lemmas. -/
lemma probEvent_eq_tsum_subtype :
  [p | oa] = ∑' x : {x | p x}, [= x | oa] := by
rw [probEvent.def, PMF.toOuterMeasure_apply, tsum_subtype, probOutput.def, setOf]

/-- Version `probEvent_eq_tsum_subtype` that preemptively filters out elements that
aren't in the support, since they will have no mass contribution anyways.
This can make some proofs simpler by handling things on the level of subtypes. -/
lemma probEvent_eq_tsum_subtype_mem_support :
    [p | oa] = ∑' x : {x ∈ oa.support | p x}, [= x | oa] := by
  simp_rw [probEvent_eq_tsum_subtype, tsum_subtype]
  refine tsum_congr (λ x ↦ ?_)
  by_cases hpx : p x
  · refine (if_pos hpx).trans ?_
    by_cases hx : x ∈ oa.support
    · simp [Set.indicator, hpx, hx]
    · simp [Set.indicator, hpx, hx, ← probOutput.def]
  · exact (if_neg hpx).trans (by simp [Set.indicator, hpx])

lemma probEvent_eq_tsum_ite [DecidablePred p] :
    [p | oa] = ∑' x : α, if p x then [= x | oa] else 0 := by
  simp_rw [probEvent.def, PMF.toOuterMeasure_apply, Set.indicator, Set.mem_def, probOutput.def]

lemma probEvent_eq_tsum_subtype_ite [DecidablePred p] :
    [p | oa] = ∑' x : oa.support, if p x then [= x | oa] else 0 :=
calc
  [p | oa] = (∑' x, if p x then [= x | oa] else 0) := by rw [probEvent_eq_tsum_ite oa p]
  _ = ∑' x, oa.support.indicator (λ x ↦ if p x then [= x | oa] else 0) x := by
    refine tsum_congr (λ x ↦ ?_)
    unfold Set.indicator
    split_ifs with h1 h2 h2 <;> simp [h1, h2]
  _ = ∑' x : oa.support, if p x then [= x | oa] else 0 := by
    rw [tsum_subtype (support oa) (λ x ↦ if p x then [= x | oa] else 0)]

lemma probEvent_eq_sum_fintype_ite [Fintype α] [DecidablePred p] :
    [p | oa] = ∑ x : α, if p x then [= x | oa] else 0 :=
  (probEvent_eq_tsum_ite oa p).trans (tsum_eq_sum' <| by simp)

lemma probEvent_eq_sum_filter_finSupport [DecidableEq α] [DecidablePred p] :
    [p | oa] = ∑ x in oa.finSupport.filter p, [= x | oa] :=
  (probEvent_eq_tsum_ite oa p).trans <| (tsum_eq_sum' <| by simp; tauto).trans
    (Finset.sum_congr rfl <| λ x hx ↦ if_pos (Finset.mem_filter.1 hx).2)

lemma probEvent_eq_sum_finSupport_ite [DecidableEq α] [DecidablePred p] :
    [p | oa] = ∑ x in oa.finSupport, if p x then [= x | oa] else 0 := by
  rw [probEvent_eq_sum_filter_finSupport, Finset.sum_filter]

end sums

@[simp] lemma probEvent_const (oa : OracleComp spec α) (p : Prop) [Decidable p] :
    [λ _ ↦ p | oa] = if p then 1 else 0 := by split_ifs with hp <;> simp [hp]

lemma probEvent_true (oa : OracleComp spec α) : [λ _ ↦ true | oa] = 1 := by simp
lemma probEvent_false (oa : OracleComp spec α) : [λ _ ↦ false | oa] = 0 := by simp

section pure

variable (x : α)

@[simp]
lemma evalDist_pure : evalDist (return x : OracleComp spec α) = PMF.pure x := rfl

@[simp]
lemma probOutput_pure [DecidableEq α] (y : α) :
    [= y | (pure x : OracleComp spec α)] = if y = x then 1 else 0 := by
  split_ifs with h
  · induction h; exact PMF.pure_apply_self y
  · exact PMF.pure_apply_of_ne _ _ h

@[simp]
lemma probEvent_pure (p : α → Prop) [DecidablePred p] :
    [p | (pure x : OracleComp spec α)] = if p x then 1 else 0 :=
  (PMF.toOuterMeasure_pure_apply x p).trans (by congr)

end pure

section bind

variable (oa : OracleComp spec α) (ob : α → OracleComp spec β)

@[simp]
lemma evalDist_bind : evalDist (oa >>= ob) = (evalDist oa).bind (evalDist ∘ ob) :=
  by induction oa using OracleComp.inductionOn with
  | h_pure _ => simp only [pure_bind, evalDist_pure, PMF.pure_bind, Function.comp_apply]
  | h_query_bind _ _ _ hoa => simp [bind_assoc, ← query_bind'_eq_query_bind, evalDist, hoa]

@[simp low]
lemma probOutput_bind_eq_tsum (y : β) :
    [= y | oa >>= ob] = ∑' x : α, [= x | oa] * [= y | ob x] :=
  by simp [probOutput.def]
@[simp low]
lemma probEvent_bind_eq_tsum (q : β → Prop) :
    [q | oa >>= ob] = ∑' x : α, [= x | oa] * [q | ob x] :=
  by simp [probEvent.def, probOutput.def]

/-- Version of `probOutput_bind_eq_tsum` that sums only over the subtype given by the support
of the first computation. This can be useful to avoid looking at edge cases that can't actually
happen in practice after the first computation. A common example is if the first computation
does some error handling to avoids returning malformed outputs. -/
lemma probOutput_bind_eq_tsum_subtype (y : β) :
    [= y | oa >>= ob] = ∑' x : oa.support, [= x | oa] * [= y | ob x] := by
  rw [tsum_subtype _ (λ x ↦ [= x | oa] * [= y | ob x]), probOutput_bind_eq_tsum]
  refine tsum_congr (λ x ↦ ?_)
  by_cases hx : x ∈ oa.support
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_not_mem hx, probOutput_eq_zero hx, zero_mul]
lemma probEvent_bind_eq_tsum_subtype (q : β → Prop) :
    [q | oa >>= ob] = ∑' x : oa.support, [= x | oa] * [q | ob x] := by
  rw [tsum_subtype _ (λ x ↦ [= x | oa] * [q | ob x]), probEvent_bind_eq_tsum]
  refine tsum_congr (λ x ↦ ?_)
  by_cases hx : x ∈ oa.support
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_not_mem hx, probOutput_eq_zero hx, zero_mul]

@[simp]
lemma probOutput_bind_eq_sum_fintype [Fintype α] (y : β) :
    [= y | oa >>= ob] = ∑ x : α, [= x | oa] * [= y | ob x] :=
  (probOutput_bind_eq_tsum oa ob y).trans (tsum_eq_sum' <| by simp)
@[simp]
lemma probEvent_bind_eq_sum_fintype [Fintype α] (q : β → Prop) :
    [q | oa >>= ob] = ∑ x : α, [= x | oa] * [q | ob x] :=
  (probEvent_bind_eq_tsum oa ob q).trans (tsum_eq_sum' <| by simp)

@[simp]
lemma probOutput_bind_eq_sum_finSupport [DecidableEq α] (y : β) :
    [= y | oa >>= ob] = ∑ x in oa.finSupport, [= x | oa] * [= y | ob x] :=
  (probOutput_bind_eq_tsum oa ob y).trans (tsum_eq_sum' <| by simp)
@[simp]
lemma probEvent_bind_eq_sum_finSupport [DecidableEq α] (q : β → Prop) :
    [q | oa >>= ob] = ∑ x in oa.finSupport, [= x | oa] * [q | ob x] :=
  (probEvent_bind_eq_tsum oa ob q).trans (tsum_eq_sum' <| by simp)

end bind

section query

variable (i : spec.ι) (t : spec.domain i)

@[simp]
lemma evalDist_query : evalDist (query i t) = PMF.ofFintype (λ _ ↦ (Fintype.card (spec.range i))⁻¹)
    (Fintype.sum_inv_card (spec.range i)) := by
  simp only [query_def, evalDist_query_bind', evalDist_pure, PMF.bind_pure]

@[simp]
lemma probOutput_query (u : spec.range i) :
    [= u | query i t] = (Fintype.card (spec.range i) : ℝ≥0∞)⁻¹ :=
  by rw [probOutput.def, evalDist_query, PMF.ofFintype_apply]

@[simp]
lemma probEvent_query_eq_mul_inv (p : spec.range i → Prop) [DecidablePred p] :
    [p | query i t] = (Finset.univ.filter p).card * (↑(Fintype.card (spec.range i)))⁻¹ := by
  simp [probEvent_eq_sum_filter_finSupport]

lemma probEvent_query_eq_inv_mul (p : spec.range i → Prop) [DecidablePred p] :
    [p | query i t] = (↑(Fintype.card (spec.range i)))⁻¹ * (Finset.univ.filter p).card := by
  rw [probEvent_query_eq_mul_inv, mul_comm]

lemma probEvent_query_eq_div (p : spec.range i → Prop) [DecidablePred p] :
    [p | query i t] = (Finset.univ.filter p).card / (Fintype.card (spec.range i)) := by
  simp [probEvent_eq_sum_filter_finSupport, div_eq_mul_inv]

end query

section map

variable (oa : OracleComp spec α) (f : α → β)

@[simp]
lemma evalDist_map : evalDist (f <$> oa) = (evalDist oa).map f := by
  simp [map_eq_bind_pure_comp, PMF.map, Function.comp]

/-- Write the probability of an output after mapping the result of a computation as a sum
over all outputs such that they map to the correct final output, using subtypes.
This lemma notably doesn't require decidable equality on the final type, unlike most
lemmas about probability when mapping a computation. -/
@[simp low]
lemma probOutput_map_eq_tsum_subtype (y : β) :
    [= y | f <$> oa] = ∑' x : {x ∈ oa.support | y = f x}, [= x | oa] := by
  have : DecidableEq β := Classical.decEq β -- TODO: shouldn't need this hack
  simp only [map_eq_bind_pure_comp, tsum_subtype _ (λ x ↦ [= x | oa]), probOutput_bind_eq_tsum,
    Function.comp_apply, probOutput_pure, mul_ite, mul_one, mul_zero,
    Set.indicator, Set.mem_setOf_eq]
  refine (tsum_congr (λ x ↦ ?_))
  by_cases hy : y = f x <;> by_cases hx : x ∈ oa.support <;> simp [hy, hx]

@[simp low]
lemma probOutput_map_eq_tsum_subtype_ite [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑' x : oa.support, if y = f x then [= x | oa] else 0 := by
  simp [map_eq_bind_pure_comp, probOutput_bind_eq_tsum_subtype]

@[simp low]
lemma probOutput_map_eq_tsum_ite [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑' x : α, if y = f x then [= x | oa] else 0 := by
  simp [map_eq_bind_pure_comp]

@[simp]
lemma probOutput_map_eq_sum_fintype_ite [Fintype α] [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑ x : α, if y = f x then [= x | oa] else 0 :=
  (probOutput_map_eq_tsum_ite oa f y).trans (tsum_eq_sum' <| by simp)

lemma probOutput_map_eq_sum_finSupport_ite [DecidableEq α] [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑ x in oa.finSupport, if y = f x then [= x | oa] else 0 :=
  (probOutput_map_eq_tsum_ite oa f y).trans
    (tsum_eq_sum' <| by simp [mem_finSupport_iff_mem_support])

@[simp]
lemma probOutput_map_eq_sum_filter_finSupport [DecidableEq α] [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑ x in oa.finSupport.filter (y = f .), [= x | oa] := by
  rw [Finset.sum_filter, probOutput_map_eq_sum_finSupport_ite]

@[simp]
lemma probEvent_map (q : β → Prop) : [q | f <$> oa] = [q ∘ f | oa] := by
  simpa [probEvent.def, evalDist_map, PMF.toOuterMeasure_map_apply] using refl _

end map

section seq

variable (oa : OracleComp spec α) (og : OracleComp spec (α → β))

@[simp]
lemma evalDist_seq : evalDist (og <*> oa) = (evalDist og).seq (evalDist oa) := by
  simp [PMF.ext_iff, seq_eq_bind_map, ← ENNReal.tsum_mul_left]

end seq

section ite

variable (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)

@[simp]
lemma evalDist_ite : evalDist (if p then oa else oa') =
    if p then evalDist oa else evalDist oa' :=
  by by_cases hp : p <;> simp [hp]

@[simp]
lemma probOutput_ite (x : α) : [= x | if p then oa else oa'] =
    if p then [= x | oa] else [= x | oa'] :=
  by by_cases hp : p <;> simp [hp]

@[simp]
lemma probEvent_ite (q : α → Prop) : [q | if p then oa else oa'] =
    if p then [q | oa] else [q | oa'] :=
  by by_cases hp : p <;> simp [hp]

end ite

section coin

@[simp]
lemma evalDist_coin : evalDist coin = PMF.bernoulli 2⁻¹ (by simp) := by
  simp [PMF.ext_iff, coin, evalDist_query (spec := coinSpec)]

@[simp]
lemma probOutput_coin (b : Bool) : [= b | coin] = 2⁻¹ := by
  simp [probOutput.def]

@[simp low]
lemma probEvent_coin_eq_sum_subtype (p : Bool → Prop) : [p | coin] = ∑' x : {x | p x}, 2⁻¹ := by
  simp [probEvent_eq_tsum_subtype]

@[simp]
lemma probEvent_coin (p : Bool → Prop) [DecidablePred p] : [p | coin] =
    if p true then (if p false then 1 else 2⁻¹) else (if p false then 2⁻¹ else 0) := by
  by_cases hpt : p true <;> by_cases hpf : p false <;>
    simp [probEvent_eq_sum_fintype_ite, hpt, hpf, inv_two_add_inv_two]

/-- The xor of two coin flips looks like flipping a single coin -/
example (x : Bool) : [= x | do let b ← coin; let b' ← coin; return xor b b'] = [= x | coin] := by
  have : (↑2 : ℝ≥0∞) ≠ ∞ := by simp
  have : (↑2 : ℝ≥0∞)⁻¹ * 2 = 1 := ENNReal.inv_mul_cancel two_ne_zero this
  cases x <;> simp [← mul_two, mul_assoc, this]

end coin

section uniformFin

variable (n : ℕ)

@[simp]
lemma evalDist_uniformFin : evalDist $[0..n] = PMF.ofFintype (λ _ ↦ ((n : ℝ≥0∞) + 1)⁻¹) (by
    have : ((n : ℝ≥0∞) + 1) * ((n : ℝ≥0∞) + 1)⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
    simpa using this) := by
  simp [PMF.ext_iff, uniformFin, evalDist_query (spec := unifSpec)]

@[simp]
lemma probOutput_uniformFin (x : Fin (n + 1)) : [= x | $[0..n]] = ((n : ℝ≥0∞) + 1)⁻¹ := by
  rw [probOutput.def, evalDist_uniformFin, PMF.ofFintype_apply]

/-- Without decidability of `p` we can't explicitly count the number of elements in the output,
so we instead express the probability of an event as a sum. -/
@[simp low]
lemma probEvent_uniformFin_eq_tsum_subtype (p : Fin (n + 1) → Prop) :
    [p | $[0..n]] = ∑' x : {x | p x}, ((n : ℝ≥0∞) + 1)⁻¹ := by
  simp [probEvent_eq_tsum_subtype]

/-- If `p` is decidable we can explicitly count the outputs of uniform selection that satisfy
the predicate, avoiding the need to include a sum. -/
@[simp]
lemma probEvent_uniformFin (p : Fin (n + 1) → Prop) [DecidablePred p] :
    [p | $[0..n]] = (Finset.univ.filter p).card * ((n : ℝ≥0∞) + 1)⁻¹ := by
  simp [probEvent_eq_sum_filter_finSupport]

end uniformFin

end OracleComp
