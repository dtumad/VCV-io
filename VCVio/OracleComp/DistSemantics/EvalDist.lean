/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.Support
import Mathlib.Probability.Distributions.Uniform
import ToMathlib.General

/-!
# Denotational Semantics for Output Distributions

This file gives definitions for the output distribution or computations with uniform oracles.
Given a computation `oa : OracleComp spec α` we define a distribution `evalDist oa : PMF α`
expressing the probability of getting an output `x : α` if the oracles in `spec` were to
respond uniformly to all queries.

We also define functions `probOutput oa x` and `probEvent oa p` for the probabilities of a
specific output of of a specific predicate holding on the output respectively.
We introduce notation `[= x | oa]` and `[p | oa]` for these defintions as well.
λ α ↦ (α → β)
The behavior of more complex oracles should first be implemented using `OracleComp.simulate`
before applying these constructions.

These definitons are compatible with `OracleComp.support` and `OracleComp.finSupport` in the sense
that values are in the support iff they have non-zero probability under `evalDist`.

We give many simp lemmas involving `tsum` a lower priority, as otherwise the simplifier will
always choose them over versions involving `sum` (as they require `DecidableEq` or `Fintype`)
-/

namespace OracleComp

open Option ENNReal BigOperators

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β : Type}

section evalDist

/-- Associate a probability mass function to a computation, where the probability is the odds of
getting a given output assuming all oracles responded uniformly at random.
NOTE: the rest can probably go in a `defs` file or something. -/
noncomputable def evalDist {α : Type} : OracleComp spec α → PMF (Option α)
  | pure' α x => PMF.pure (some x)
  | queryBind' i _ α oa =>
      (PMF.uniformOfFintype (spec.range i)).bind (λ u ↦ evalDist (oa u))
  | failure' α => PMF.pure none

@[simp]
lemma evalDist_pure (x : α) : evalDist (pure x : OracleComp spec α) = PMF.pure (some x) := rfl

@[simp]
lemma evalDist_query (i : ι) (t : spec.domain i) :
    evalDist (query i t) = (PMF.uniformOfFintype (spec.range i)).map some := rfl

@[simp]
lemma evalDist_failure : evalDist (failure : OracleComp spec α) = PMF.pure none := rfl

@[simp]
lemma evalDist_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    evalDist (oa >>= ob) = (evalDist oa).bind (Option.rec (PMF.pure none) (evalDist ∘ ob)) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp only [pure_bind, evalDist_pure, PMF.pure_bind, Function.comp_apply]
  | query_bind i t oa hoa => simp [← queryBind'_eq_queryBind, evalDist, hoa]
  | failure => simp only [failure_bind, evalDist_failure, PMF.pure_bind]

lemma evalDist_query_bind (i : ι) (t : spec.domain i) (ou : spec.range i → OracleComp spec α) :
    evalDist (query i t >>= ou) = (PMF.uniformOfFintype (spec.range i)).bind (evalDist ∘ ou) := rfl

@[simp]
lemma evalDist_map (oa : OracleComp spec α) (f : α → β) :
    evalDist (f <$> oa) = (evalDist oa).map (Option.map f) := by
  rw [map_eq_bind_pure_comp, evalDist_bind, PMF.map]
  refine congr_arg (oa.evalDist.bind ·) (funext λ x ↦ ?_)
  cases x <;> simp

@[simp]
lemma evalDist_eqRec (h : α = β) (oa : OracleComp spec α) :
  evalDist (h ▸ oa) = h ▸ evalDist oa := by induction h; rfl

@[simp]
lemma evalDist_ite (p : Prop) [Decidable p] (oa oa' : OracleComp spec α) :
    evalDist (if p then oa else oa') = if p then evalDist oa else evalDist oa' := by
  by_cases hp : p <;> simp [hp]

@[simp]
lemma evalDist_coin : evalDist coin = (PMF.bernoulli 2⁻¹ (by simp)).map some := by
  rw [coin, evalDist_query]
  refine PMF.ext λ x ↦ by simp

@[simp]
lemma evalDist_uniformFin (n : ℕ) :
    evalDist $[0..n] = (PMF.uniformOfFintype (Fin (n + 1))).map some := by
  simp only [uniformFin, evalDist_query (spec := unifSpec)]

end evalDist

/-- `[= x | oa]` is the probability of getting the given output `x` from the computation `oa`,
assuming all oracles respond uniformly at random. -/
noncomputable def probOutput (oa : OracleComp spec α) (x : α) : ℝ≥0∞ := evalDist oa (some x)

notation "[=" x "|" oa "]" => probOutput oa x

/-- `[⊥ | oa]` is the probability of the computation `oa` failing. -/
noncomputable def probFailure (oa : OracleComp spec α) : ℝ≥0∞ := evalDist oa none

notation "[⊥" "|" oa "]" => probFailure oa

/-- `[p | oa]` is the probability of getting a result that satisfies a predicate `p`
after running the computation `oa`, assuming all oracles respond uniformly at random.-/
noncomputable def probEvent (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] : ℝ≥0∞ :=
  ∑' x : α, if p x then [= x | oa] else 0
--(evalDist oa).toOuterMeasure (Option.some '' {x | p x}) NOTE: would avoid decidability this way.

notation "[" p "|" oa "]" => probEvent oa p

lemma evalDist_apply_some (oa : OracleComp spec α) (x : α) :
    evalDist oa (some x) = [= x | oa] := rfl
lemma evalDist_apply_none (oa : OracleComp spec α) :
    evalDist oa none = [⊥ | oa] := rfl

lemma probOutput_def (oa : OracleComp spec α) (x : α) :
    [= x | oa] = evalDist oa (some x) := rfl
lemma probFailure_def (oa : OracleComp spec α) :
    [⊥ | oa] = evalDist oa none := rfl
lemma probEvent_def (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    [p | oa] = ∑' x : α, if p x then [= x | oa] else 0 := rfl

noncomputable example : ℝ≥0∞ := [= 5 | do let x ←$[0..4]; return x + 1]
noncomputable example : ℝ≥0∞ := [⊥ | do let x ←$[0..4]; if x = 0 then failure else return x]
noncomputable example : ℝ≥0∞ := [(· + 1 ≤ 3) | do let x ←$[0..4]; return x]

@[simp]
lemma probFailure_add_tsum_probOutput (oa : OracleComp spec α) :
    [⊥ | oa] + ∑' x, [= x | oa] = 1 :=
  (tsum_option _ ENNReal.summable).symm.trans (evalDist oa).tsum_coe

@[simp]
lemma tsum_probOutput_add_probFailure (oa : OracleComp spec α) :
    ∑' x, [= x | oa] + [⊥ | oa] = 1 :=
  by rw [add_comm, probFailure_add_tsum_probOutput]

section bounds

variable {oa : OracleComp spec α} {x : α} {p : α → Prop} [DecidablePred p]

@[simp] lemma probOutput_le_one : [= x | oa] ≤ 1 := PMF.coe_le_one (evalDist oa) x
@[simp] lemma probFailure_le_one : [⊥ | oa] ≤ 1 := PMF.coe_le_one (evalDist oa) none

@[simp] lemma tsum_probOutput_le_one : ∑' x : α, [= x | oa] ≤ 1 :=
  le_of_le_of_eq (le_add_self) (probFailure_add_tsum_probOutput oa)
@[simp] lemma probEvent_le_one : [p | oa] ≤ 1 :=
  le_trans (ENNReal.tsum_le_tsum (λ x ↦ by split_ifs <;> simp)) (tsum_probOutput_le_one (oa := oa))

@[simp] lemma probOutput_ne_top : [= x | oa] ≠ ∞ := PMF.apply_ne_top (evalDist oa) x
@[simp] lemma probOutput_lt_top : [= x | oa] < ∞ := PMF.apply_lt_top (evalDist oa) x
@[simp] lemma probEvent_ne_top : [p | oa] ≠ ∞ := ne_top_of_le_ne_top one_ne_top probEvent_le_one
@[simp] lemma probEvent_lt_top : [p | oa] < ∞ := lt_top_iff_ne_top.2 probEvent_ne_top
@[simp] lemma probFailure_ne_top : [⊥ | oa] ≠ ∞ := PMF.apply_ne_top (evalDist oa) none
@[simp] lemma probFailure_lt_top : [⊥ | oa] < ∞ := PMF.apply_lt_top (evalDist oa) none

end bounds

lemma tsum_probOutput_eq_sub (oa : OracleComp spec α) :
    ∑' x, [= x | oa] = 1 - [⊥ | oa] := by
  refine ENNReal.eq_sub_of_add_eq probFailure_ne_top (tsum_probOutput_add_probFailure oa)

lemma probFailure_eq_sub (oa : OracleComp spec α) :
    [⊥ | oa] = 1 - ∑' x, [= x | oa] := by
  refine ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
    (probFailure_add_tsum_probOutput oa)

section support

variable (oa : OracleComp spec α) (x : α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]

/-- An output has non-zero probability iff it is in the `support` of the computation. -/
@[simp]
lemma mem_support_evalDist_iff (oa : OracleComp spec α) (x : α) :
    some x ∈ (evalDist oa).support ↔ x ∈ oa.support := by
  induction oa using OracleComp.inductionOn with
  | pure => simp
  | query_bind i t oa hoa => simp [hoa]
  | failure => simp
alias ⟨mem_support_of_mem_support_evalDist, mem_support_evalDist⟩ := mem_support_evalDist_iff

/-- An output has non-zero probability iff it is in the `finSupport` of the computation. -/
@[simp]
lemma mem_support_evalDist_iff' [DecidableEq α] (oa : OracleComp spec α) (x : α) :
    some x ∈ (evalDist oa).support ↔ x ∈ oa.finSupport := by
  rw [mem_support_evalDist_iff, mem_finSupport_iff_mem_support]
alias ⟨mem_finSupport_of_mem_support_evalDist, mem_support_evalDist'⟩ := mem_support_evalDist_iff'

@[simp]
lemma evalDist_apply_eq_zero_iff (x : Option α) :
    evalDist oa x = 0 ↔ x.rec ([⊥ | oa] = 0) (· ∉ oa.support) :=
  match x with
  | none => by simp [probFailure_def]
  | some x => by simp [← mem_support_evalDist_iff]

@[simp]
lemma evalDist_apply_eq_zero_iff' [DecidableEq α] (x : Option α) :
    evalDist oa x = 0 ↔ x.rec ([⊥ | oa] = 0) (· ∉ oa.finSupport) := by
  simp [← mem_support_evalDist_iff']

/-- The support of `evalDist oa` is exactly `support oa`. -/
lemma support_evalDist : (evalDist oa).support = if [⊥ | oa] = 0 then
    some '' oa.support else insert none (some '' oa.support) := by
  rw [probFailure_def]
  refine Set.ext (λ x ↦ x.rec ?_ ?_)
  · split_ifs with h <;> simp [h]
  · split_ifs <;> simp

lemma support_evalDist' [DecidableEq α] : (evalDist oa).support = if [⊥ | oa] = 0 then
    oa.finSupport.image some else insert none (oa.finSupport.image some) := by
  rw [support_evalDist]
  split_ifs with h <;> simp only [Finset.coe_insert, Finset.coe_image, coe_finSupport]

@[simp low]
lemma probOutput_eq_zero_iff : [= x | oa] = 0 ↔ x ∉ oa.support := by
  rw [probOutput, PMF.apply_eq_zero_iff, mem_support_evalDist_iff]
alias ⟨not_mem_support_of_probOutput_eq_zero, probOutput_eq_zero⟩ := probOutput_eq_zero_iff

@[simp]
lemma probOutput_eq_zero_iff' [DecidableEq α] : [= x | oa] = 0 ↔ x ∉ oa.finSupport := by
  rw [mem_finSupport_iff_mem_support, probOutput_eq_zero_iff]
alias ⟨not_mem_fin_support_of_probOutput_eq_zero, probOutput_eq_zero'⟩ := probOutput_eq_zero_iff

@[simp low]
lemma probEvent_eq_zero_iff : [p | oa] = 0 ↔ ∀ x ∈ oa.support, ¬ p x := by
  suffices (∀ x, p x → x ∉ oa.support) ↔ ∀ x ∈ oa.support, ¬p x
  by simpa [probEvent] using this
  exact forall_congr' λ _ ↦ imp_not_comm
alias ⟨not_of_mem_support_of_probEvent_eq_zero, probEvent_eq_zero⟩ := probEvent_eq_zero_iff

@[simp]
lemma probEvent_eq_zero_iff' [DecidableEq α] : [p | oa] = 0 ↔ ∀ x ∈ oa.finSupport, ¬ p x := by
  simp only [probEvent_eq_zero_iff, mem_finSupport_iff_mem_support]
alias ⟨not_of_mem_finSupport_of_probEvent_eq_zero, probEvent_eq_zero'⟩ := probEvent_eq_zero_iff'

@[simp low]
lemma probOutput_pos_iff : 0 < [= x | oa] ↔ x ∈ oa.support := by
  rw [pos_iff_ne_zero, ne_eq, probOutput_eq_zero_iff, not_not]
alias ⟨mem_support_of_probOutput_pos, probOutput_pos⟩ := probOutput_pos_iff

@[simp]
lemma probOutput_pos_iff' [DecidableEq α] : 0 < [= x | oa] ↔ x ∈ oa.finSupport := by
  rw [probOutput_pos_iff, mem_finSupport_iff_mem_support]
alias ⟨mem_finSupport_of_probOutput_pos, probOutput_pos'⟩ := probOutput_pos_iff'

@[simp low]
lemma probEvent_pos_iff : 0 < [p | oa] ↔ ∃ x ∈ oa.support, p x := by
  simp_rw [pos_iff_ne_zero, ne_eq, probEvent_eq_zero_iff, not_forall, not_not, exists_prop]
alias ⟨exists_mem_support_of_probEvent_pos, probEvent_pos⟩ := probEvent_pos_iff

@[simp]
lemma probEvent_pos_iff' [DecidableEq α] : 0 < [p | oa] ↔ ∃ x ∈ oa.finSupport, p x := by
  simp_rw [pos_iff_ne_zero, ne_eq, probEvent_eq_zero_iff', not_forall, not_not, exists_prop]
alias ⟨exists_mem_finSupport_of_probEvent_pos, probEvent_pos'⟩ := probEvent_pos_iff'

@[simp low]
lemma probOutput_eq_one_iff :
    [= x | oa] = 1 ↔ [⊥ | oa] = 0 ∧ oa.support = {x} := by
  simp [probOutput_def, PMF.apply_eq_one_iff, Set.ext_iff, Option.forall]
alias ⟨_, probOutput_eq_one⟩ := probOutput_eq_one_iff

@[simp]
lemma probOutput_eq_one_iff' [DecidableEq α] :
    [= x | oa] = 1 ↔ [⊥ | oa] = 0 ∧ oa.finSupport = {x} := by
  rw [probOutput_eq_one_iff, finSupport_eq_iff_support_eq_coe, Finset.coe_singleton]
alias ⟨_, probOutput_eq_one'⟩ := probOutput_eq_one_iff'

@[simp low]
lemma probEvent_eq_one_iff :
    [p | oa] = 1 ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.support, p x := by
  rw [probEvent]
  rw [← tsum_probOutput_add_probFailure oa]
  sorry
alias ⟨_, probEvent_eq_one⟩ := probEvent_eq_one_iff

@[simp]
lemma probEvent_eq_one_iff' [DecidableEq α] :
    [p | oa] = 1 ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.finSupport, p x := by
  simp_rw [probEvent_eq_one_iff, mem_finSupport_iff_mem_support]
alias ⟨_, probEvent_eq_one'⟩ := probEvent_eq_one_iff'

lemma mem_support_iff_probOutput_ne_zero : x ∈ oa.support ↔ [= x | oa] ≠ 0 := by
  simp only [ne_eq, probOutput_eq_zero_iff, not_not]
lemma mem_support_iff_probOutput_pos : x ∈ oa.support ↔ 0 < [= x | oa] := by
  simp only [probOutput_pos_iff]
lemma not_mem_support_iff_probOutput_eq_zero : x ∉ oa.support ↔ [= x | oa] = 0 := by
  simp only [probOutput_eq_zero_iff]

variable {oa x p q}

/-- If `p` implies `q` on the `support` of a computation then it is more likely to happen. -/
lemma probEvent_mono (h : ∀ x ∈ oa.support, p x → q x) : [p | oa] ≤ [q | oa] := by
  refine tsum_mono ENNReal.summable ENNReal.summable (λ x ↦ ?_)
  by_cases hx : x ∈ oa.support
  · by_cases hpx : p x
    · simp [hpx, h x hx hpx]
    · simp [hpx]
  · simp [probOutput_eq_zero oa x hx]

/-- If `p` implies `q` on the `finSupport` of a computation then it is more likely to happen. -/
lemma probEvent_mono' [DecidableEq α] (h : ∀ x ∈ oa.finSupport, p x → q x) : [p | oa] ≤ [q | oa] :=
  probEvent_mono (λ x hx hpx ↦ h x (mem_finSupport_of_mem_support oa hx) hpx)


-- NOTE: should allow `p` and `q` to differ outside the shared support.
lemma probEvent_congr {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h1 : ∀ x, p x ↔ q x) (h2 : evalDist oa = evalDist oa') : [p | oa] = [q | oa'] := by
  simp only [probEvent, probOutput, h1, h2]

lemma probEvent_ext (h : ∀ x ∈ oa.support, p x ↔ q x) : [p | oa] = [q | oa] :=
  le_antisymm (probEvent_mono <| λ x hx hp ↦ (h x hx).1 hp)
    (probEvent_mono <| λ x hx hp ↦ (h x hx).2 hp)

lemma probEvent_ext' [DecidableEq α] (h : ∀ x ∈ oa.finSupport, p x ↔ q x) : [p | oa] = [q | oa] :=
  le_antisymm (probEvent_mono' <| λ x hx hp ↦ (h x hx).1 hp)
    (probEvent_mono' <| λ x hx hp ↦ (h x hx).2 hp)

@[simp]
lemma function_support_probOutput : Function.support ([= · | oa]) = oa.support := by
  simp only [Function.support, ne_eq, probOutput_eq_zero_iff, not_not, Set.setOf_mem_eq]

lemma mem_support_iff_of_evalDist_eq {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h : evalDist oa = evalDist oa') (x : α) : x ∈ oa.support ↔ x ∈ oa'.support := by
  simp only [mem_support_iff_probOutput_ne_zero, probOutput_def, h]

lemma mem_finSupport_iff_of_evalDist_eq [DecidableEq α]
    {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h : evalDist oa = evalDist oa') (x : α) : x ∈ oa.finSupport ↔ x ∈ oa'.finSupport := by
  simp only [mem_finSupport_iff_mem_support, mem_support_iff_of_evalDist_eq h]

end support

@[simp] lemma probEvent_eq_eq_probOutput [DecidableEq α] (oa : OracleComp spec α) (x : α) :
    [(· = x) | oa] = [= x | oa] :=
  (tsum_eq_single x (λ y ↦ by simp; tauto;)).trans (if_pos rfl)

@[simp] lemma probEvent_eq_eq_probOutput' [DecidableEq α] (oa : OracleComp spec α) (x : α) :
    [(x = ·) | oa] = [= x | oa] :=
  (probEvent_congr (λ _ ↦ eq_comm) rfl).trans (probEvent_eq_eq_probOutput oa x)

section sums

variable (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p]

/-- The probability of an event written as a sum over the set `{x | p x}` viewed as a subtype.
This notably doesn't require decidability of the predicate `p` unlike many other lemmas. -/
lemma probEvent_eq_tsum_subtype :
    [p | oa] = ∑' x : {x | p x}, [= x | oa] := by
  rw [probEvent_def, tsum_subtype]
  refine tsum_congr (λ x ↦ ?_)
  split_ifs with hx <;> simp [hx]

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
    · simp only [Set.indicator, Set.mem_setOf_eq, hx, hpx, and_self, ↓reduceIte]
    · simp only [Set.indicator, Set.mem_setOf_eq, hx, hpx, and_true, ↓reduceIte,
      probOutput_eq_zero_iff, not_false_eq_true]
  · exact (if_neg hpx).trans (by simp [Set.indicator, hpx])

lemma probEvent_eq_tsum_subtype_support_ite :
    [p | oa] = ∑' x : oa.support, if p x then [= x | oa] else 0 :=
calc
  [p | oa] = (∑' x, if p x then [= x | oa] else 0) := by rw [probEvent_def oa p]
  _ = ∑' x, oa.support.indicator (λ x ↦ if p x then [= x | oa] else 0) x := by
    refine tsum_congr (λ x ↦ ?_)
    unfold Set.indicator
    split_ifs with h1 h2 h2 <;> simp [h1, h2]
  _ = ∑' x : oa.support, if p x then [= x | oa] else 0 := by
    rw [tsum_subtype (support oa) (λ x ↦ if p x then [= x | oa] else 0)]

lemma probEvent_eq_sum_fintype_ite [Fintype α] :
    [p | oa] = ∑ x : α, if p x then [= x | oa] else 0 :=
  (tsum_eq_sum' <| by simp)

lemma probEvent_eq_sum_filter_univ [Fintype α] :
    [p | oa] = ∑ x in Finset.univ.filter p, [= x | oa] := by
  rw [probEvent_eq_sum_fintype_ite, Finset.sum_filter]

lemma probEvent_eq_sum_filter_finSupport [DecidableEq α] :
    [p | oa] = ∑ x in oa.finSupport.filter p, [= x | oa] :=
  (tsum_eq_sum' <| by simp; tauto).trans
    (Finset.sum_congr rfl <| λ x hx ↦ if_pos (Finset.mem_filter.1 hx).2)

lemma probEvent_eq_sum_finSupport_ite [DecidableEq α] :
    [p | oa] = ∑ x in oa.finSupport, if p x then [= x | oa] else 0 := by
  rw [probEvent_eq_sum_filter_finSupport, Finset.sum_filter]

end sums

lemma probOutput_congr {x y : α} {oa oa' : OracleComp spec α}
    (h1 : x = y) (h2 : evalDist oa = evalDist oa') : [= x | oa] = [= y | oa'] := by
  simp_rw [probOutput, h1, h2]

lemma probEvent_congr' {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    {oa oa' : OracleComp spec α}
    (h1 : ∀ x, x ∈ oa.support → x ∈ oa'.support → (p x ↔ q x))
    (h2 : evalDist oa = evalDist oa') : [p | oa] = [q | oa'] := by
  have h : ∀ x, x ∈ oa.support ↔ x ∈ oa'.support := by
    refine mem_support_iff_of_evalDist_eq h2
  simp [probEvent, probOutput_congr rfl h2]
  refine tsum_congr (λ x ↦ ?_)
  specialize h1 x
  split_ifs with hp hq hq
  · rfl
  · simpa [h, hp, hq] using h1
  · symm; simpa [h, hp, hq] using h1
  · rfl

@[simp] lemma probEvent_const (oa : OracleComp spec α) (p : Prop) [Decidable p] :
    [λ _ ↦ p | oa] = if p then 1 - [⊥ | oa] else 0 := by
  split_ifs with hp <;> simp [hp, probEvent, tsum_probOutput_eq_sub]

lemma probEvent_true (oa : OracleComp spec α) : [λ _ ↦ true | oa] = 1 - [⊥ | oa] := by simp
lemma probEvent_false (oa : OracleComp spec α) : [λ _ ↦ false | oa] = 0 := by simp

lemma evalDist_ext_probEvent {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h : ∀ x, [= x | oa] = [= x | oa']) : evalDist oa = evalDist oa' :=
  PMF.ext λ x ↦ match x with
  | none => by simp [← probFailure_def, probFailure_eq_sub, h]
  | some x => h x

section pure

variable (x : α)

@[simp]
lemma probOutput_pure [DecidableEq α] (y : α) :
    [= y | (pure x : OracleComp spec α)] = if y = x then 1 else 0 := by simp [probOutput]

@[simp]
lemma probFailure_pure : [⊥ | (pure x : OracleComp spec α)] = 0 := by simp [probFailure]

lemma probOutput_pure_eq_zero {x y : α} (h : y ≠ x) :
    [= y | (pure x : OracleComp spec α)] = 0 := by simpa using h

lemma probOutput_pure_eq_one {x y : α} (h : y = x) :
    [= y | (pure x : OracleComp spec α)] = 1 := by simpa using h.symm

@[simp]
lemma probOutput_pure_self (x : α) : [= x | (pure x : OracleComp spec α)] = 1 := by simp

@[simp]
lemma probOutput_pure_subsingleton [Subsingleton α] (x y : α) :
    [= x | (pure y : OracleComp spec α)] = 1 := by
  simp [Subsingleton.elim x y]

@[simp]
lemma probEvent_pure (p : α → Prop) [DecidablePred p] :
    [p | (pure x : OracleComp spec α)] = if p x then 1 else 0 := by
  simp [probEvent]
  refine (tsum_eq_single x (by simp; tauto)).trans (by simp)

end pure

section bind

variable (oa : OracleComp spec α) (ob : α → OracleComp spec β)

lemma probOutput_bind_eq_tsum (y : β) :
    [= y | oa >>= ob] = ∑' x : α, [= x | oa] * [= y | ob x] := by
  simp [probOutput, evalDist_bind, tsum_option _ ENNReal.summable]

lemma probFailure_bind_eq_tsum :
    [⊥ | oa >>= ob] = [⊥ | oa] + ∑' x : α, [= x | oa] * [⊥ | ob x] := by
  simp [probFailure, evalDist_bind, tsum_option _ ENNReal.summable, ← probOutput_def]

lemma probEvent_bind_eq_tsum (q : β → Prop) [DecidablePred q] :
    [q | oa >>= ob] = ∑' x : α, [= x | oa] * [q | ob x] := by
  simp only [probOutput_bind_eq_tsum, probEvent, ← ENNReal.tsum_mul_left]
  refine (tsum_congr (λ y ↦ ?_)).trans ENNReal.tsum_comm
  split_ifs with hqy <;> simp

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
  · rw [Set.indicator_of_not_mem hx, probOutput_eq_zero _ _ hx, zero_mul]

lemma probEvent_bind_eq_tsum_subtype (q : β → Prop) [DecidablePred q] :
    [q | oa >>= ob] = ∑' x : oa.support, [= x | oa] * [q | ob x] := by
  rw [tsum_subtype _ (λ x ↦ [= x | oa] * [q | ob x]), probEvent_bind_eq_tsum]
  refine tsum_congr (λ x ↦ ?_)
  by_cases hx : x ∈ oa.support
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_not_mem hx, probOutput_eq_zero _ _ hx, zero_mul]

lemma probOutput_bind_eq_sum_fintype [Fintype α] (y : β) :
    [= y | oa >>= ob] = ∑ x : α, [= x | oa] * [= y | ob x] :=
  (probOutput_bind_eq_tsum oa ob y).trans (tsum_eq_sum' <| by simp)

lemma probFailure_bind_eq_sum_fintype [Fintype α] :
    [⊥ | oa >>= ob] = [⊥ | oa] + ∑ x : α, [= x | oa] * [⊥ | ob x] :=
  (probFailure_bind_eq_tsum oa ob).trans (congr_arg ([⊥ | oa] + ·) <| tsum_eq_sum' <| by simp)

lemma probEvent_bind_eq_sum_fintype [Fintype α] (q : β → Prop) [DecidablePred q] :
    [q | oa >>= ob] = ∑ x : α, [= x | oa] * [q | ob x] :=
  (probEvent_bind_eq_tsum oa ob q).trans (tsum_eq_sum' <| by simp)

lemma probOutput_bind_eq_sum_finSupport [DecidableEq α] (y : β) :
    [= y | oa >>= ob] = ∑ x in oa.finSupport, [= x | oa] * [= y | ob x] :=
  (probOutput_bind_eq_tsum oa ob y).trans (tsum_eq_sum' <| by simp)

lemma probEvent_bind_eq_sum_finSupport [DecidableEq α] (q : β → Prop) [DecidablePred q] :
    [q | oa >>= ob] = ∑ x in oa.finSupport, [= x | oa] * [q | ob x] :=
  (probEvent_bind_eq_tsum oa ob q).trans (tsum_eq_sum' <| by simp)

end bind

section query

variable (i : ι) (t : spec.domain i)

@[simp]
lemma probOutput_query (u : spec.range i) :
    [= u | query i t] = (Fintype.card (spec.range i) : ℝ≥0∞)⁻¹ := by
  simp [probOutput]
  refine (tsum_eq_single u ?_).trans (if_pos rfl)
  simp [@eq_comm _ u]

@[simp]
lemma probFailure_query : [⊥ | query i t] = 0 := by simp [probFailure]

@[simp]
lemma probEvent_query_eq_mul_inv (p : spec.range i → Prop) [DecidablePred p] :
    [p | query i t] = (Finset.univ.filter p).card * (↑(Fintype.card (spec.range i)))⁻¹ := by
  simp only [probEvent_eq_sum_filter_finSupport, finSupport_query, probOutput_query,
    Finset.sum_const, nsmul_eq_mul]

lemma probEvent_query_eq_inv_mul (p : spec.range i → Prop) [DecidablePred p] :
    [p | query i t] = (↑(Fintype.card (spec.range i)))⁻¹ * (Finset.univ.filter p).card := by
  rw [probEvent_query_eq_mul_inv, mul_comm]

lemma probEvent_query_eq_div (p : spec.range i → Prop) [DecidablePred p] :
    [p | query i t] = (Finset.univ.filter p).card / (Fintype.card (spec.range i)) := by
  simp only [probEvent_eq_sum_filter_finSupport, finSupport_query, probOutput_query,
    Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

end query

section failure

@[simp]
lemma probOutput_failure (x : α) : [= x | (failure : OracleComp spec α)] = 0 := by simp

@[simp]
lemma probFailure_failure : [⊥ | (failure : OracleComp spec α)] = 1 := by simp [probFailure]

@[simp]
lemma probEvent_failure (p : α → Prop) [DecidablePred p] :
  [p | (failure : OracleComp spec α)] = 0 := by simp

end failure

section map

variable (oa : OracleComp spec α) (f : α → β)

/-- Write the probability of an output after mapping the result of a computation as a sum
over all outputs such that they map to the correct final output, using subtypes.
This lemma notably doesn't require decidable equality on the final type, unlike most
lemmas about probability when mapping a computation. -/
lemma probOutput_map_eq_tsum_subtype (y : β) :
    [= y | f <$> oa] = ∑' x : {x ∈ oa.support | y = f x}, [= x | oa] := by
  simp only [map_eq_bind_pure_comp, tsum_subtype _ (λ x ↦ [= x | oa]), probOutput_bind_eq_tsum,
    Function.comp_apply, probOutput_pure, mul_ite, mul_one, mul_zero,
    Set.indicator, Set.mem_setOf_eq]
  refine (tsum_congr (λ x ↦ ?_))
  by_cases hy : y = f x <;> by_cases hx : x ∈ oa.support <;> simp [hy, hx]

lemma probOutput_map_eq_tsum (y : β) :
    [= y | f <$> oa] = ∑' x, [= x | oa] * [= y | (pure (f x) : OracleComp spec β)] := by
  simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum, Function.comp_apply]

lemma probOutput_map_eq_tsum_subtype_ite [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑' x : oa.support, if y = f x then [= x | oa] else 0 := by
  simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum_subtype, Function.comp_apply,
    probOutput_pure, mul_ite, mul_one, mul_zero]

lemma probOutput_map_eq_tsum_ite [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑' x : α, if y = f x then [= x | oa] else 0 := by
  simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum, Function.comp_apply, probOutput_pure,
    mul_ite, mul_one, mul_zero]

lemma probOutput_map_eq_sum_fintype_ite [Fintype α] [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑ x : α, if y = f x then [= x | oa] else 0 :=
  (probOutput_map_eq_tsum_ite oa f y).trans (tsum_eq_sum' <|
    by simp only [Finset.coe_univ, Set.subset_univ])

lemma probOutput_map_eq_sum_finSupport_ite [DecidableEq α] [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑ x in oa.finSupport, if y = f x then [= x | oa] else 0 :=
  (probOutput_map_eq_tsum_ite oa f y).trans (tsum_eq_sum' <|
    by simp only [coe_finSupport, Function.support_subset_iff, ne_eq, ite_eq_right_iff,
      probOutput_eq_zero_iff', mem_finSupport_iff_mem_support, Classical.not_imp, not_not, and_imp,
      imp_self, implies_true])

lemma probOutput_map_eq_sum_filter_finSupport [DecidableEq α] [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑ x in oa.finSupport.filter (y = f ·), [= x | oa] := by
  rw [Finset.sum_filter, probOutput_map_eq_sum_finSupport_ite]

@[simp]
lemma probFailure_map : [⊥ | f <$> oa] = [⊥ | oa] := by
  simp only [probFailure, evalDist_map, PMF.map_apply]
  refine (tsum_eq_single none λ x ↦ ?_).trans (if_pos rfl)
  cases x <;> simp

@[simp]
lemma probEvent_map (q : β → Prop) [DecidablePred q] : [q | f <$> oa] = [q ∘ f | oa] := by
  simp [probEvent, probOutput]
  sorry
  -- simp only [probEvent_def, evalDist_map, PMF.toOuterMeasure_map_apply]; congr

lemma probEvent_comp (q : β → Prop) [DecidablePred q] : [q ∘ f | oa] = [q | f <$> oa] :=
  symm <| probEvent_map oa f q

lemma probOutput_map_eq_probOutput_inverse (f : α → β) (g : β → α)
    (hl : Function.LeftInverse f g) (hr : Function.RightInverse f g)
    (y : β) : [= y | f <$> oa] = [= g y | oa] := by
  rw [probOutput_map_eq_tsum]
  refine (tsum_eq_single (g y) (λ x hx ↦ ?_)).trans ?_
  · suffices y ≠ f x by simp [this]
    exact (λ h ↦ hx ((congr_arg g h).trans (hr x)).symm)
  · simp [hl y]

end map

section eqRec

variable (oa : OracleComp spec α) (h : α = β)

lemma probOutput_eqRec (y : β) : [= y | h ▸ oa] = [= h ▸ y | oa] := by induction h; rfl
lemma probFailure_eqRec : [⊥ | h ▸ oa] = [⊥ | oa] := by induction h; rfl
lemma probEvent_eqRec (q : β → Prop) [DecidablePred q] :
    [q | h ▸ oa] = [λ x ↦ q (h ▸ x) | oa] := by induction h; rfl

end eqRec

section ite

variable (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)

@[simp]
lemma probOutput_ite (x : α) : [= x | if p then oa else oa'] =
    if p then [= x | oa] else [= x | oa'] := by
  by_cases hp : p <;> simp [hp]

@[simp]
lemma probFailure_ite : [⊥ | if p then oa else oa'] =
    if p then [⊥ | oa] else [⊥ | oa'] := by
  by_cases hp : p <;> simp [hp]

@[simp]
lemma probEvent_ite (q : α → Prop) [DecidablePred q] : [q | if p then oa else oa'] =
    if p then [q | oa] else [q | oa'] := by
  by_cases hp : p <;> simp [hp]

end ite

section coin

@[simp]
lemma probOutput_coin (b : Bool) : [= b | coin] = 2⁻¹ := by
  cases b <;> simp [probOutput]

lemma probEvent_coin_eq_sum_subtype (p : Bool → Prop) [DecidablePred p] :
    [p | coin] = ∑' _ : {x | p x}, 2⁻¹ := by
  simp only [probEvent_eq_tsum_subtype, Set.coe_setOf, Set.mem_setOf_eq, probOutput_coin]

@[simp]
lemma probEvent_coin (p : Bool → Prop) [DecidablePred p] : [p | coin] =
    if p true then (if p false then 1 else 2⁻¹) else (if p false then 2⁻¹ else 0) := by
  by_cases hpt : p true <;> by_cases hpf : p false <;>
    simp [probEvent, tsum_bool, hpt, hpf, inv_two_add_inv_two]

lemma probEvent_coin_eq_add (p : Bool → Prop) [DecidablePred p] :
    [p | coin] = (if p true then 2⁻¹ else 0) + (if p false then 2⁻¹ else 0) := by
  rw [probEvent_coin]; split_ifs <;> simp [inv_two_add_inv_two]

-- /-- The xor of two coin flips looks like flipping a single coin -/
-- example (x : Bool) : [= x | do let b ← coin; let b' ← coin; return xor b b'] = [= x | coin] := by
--   have : (↑2 : ℝ≥0∞) ≠ ∞ := by simp
--   cases x <;> simp [← mul_two, mul_comm (2 : ℝ≥0∞), mul_assoc,
--     ENNReal.inv_mul_cancel two_ne_zero this, probOutput_bind_eq_sum_fintype]
--   ·

end coin

section uniformFin

variable (n : ℕ)

@[simp]
lemma probOutput_uniformFin (x : Fin (n + 1)) : [= x | $[0..n]] = ((n : ℝ≥0∞) + 1)⁻¹ := by
  simp [uniformFin, probOutput_query (spec := unifSpec)]

@[simp]
lemma probFailure_uniformFin : [⊥ | $[0..n]] = 0 := probFailure_query _ _

@[simp]
lemma probEvent_uniformFin (p : Fin (n + 1) → Prop) [DecidablePred p] :
    [p | $[0..n]] = (Finset.univ.filter p).card * (n + 1 : ℝ≥0∞)⁻¹ := by
  simp only [probEvent_eq_sum_filter_finSupport, finSupport_uniformFin, probOutput_uniformFin,
    Finset.sum_const, nsmul_eq_mul]

end uniformFin

@[simp]
lemma guard_eq (p : Prop) [Decidable p] :
    (guard p : OracleComp spec Unit) = if p then pure () else failure := rfl

/-- Example of brute forcing a probability computation by expanding terms and using `ring_nf`. -/
example : [⊥ | do
    let x ←$[0..5]; let y ←$[0..3]
    guard (x = 0); guard (y ≠ x); return ()] = 21 / 24 := by
  -- NOTE: would be nice not to need arithmetic facts
  have : (6 : ℝ≥0∞)⁻¹ * (4 : ℝ≥0∞)⁻¹ = (24 : ℝ≥0∞)⁻¹ :=
    by rw [← ENNReal.mul_inv (by tauto) (by tauto)]; ring_nf
  simp [probFailure_bind_eq_sum_fintype, Fin.sum_univ_succ, Fin.succ_ne_zero,
    div_eq_mul_inv, this]
  ring_nf
  rw [this]

end OracleComp
