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

/-- Backend definition for `evalDist`, mapping each query to a uniform distribution,
lifting into the `OptionT` type to handle `failure`.
The actual `evalDist` definition just runs the option transformer layer. -/
noncomputable def evalDistT {α : Type} (oa : OracleComp spec α) : OptionT PMF α := by
  refine oa.mapM λ i t ↦ OptionT.lift (PMF.uniformOfFintype (spec.range i))

/-- Associate a probability mass function to a computation, where the probability is the odds of
getting a given output assuming all oracles responded uniformly at random.
NOTE: the rest can probably go in a `defs` file or something. -/
noncomputable def evalDist {α : Type} (oa : OracleComp spec α) :
    PMF (Option α) := oa.evalDistT.run

@[simp]
lemma evalDist_pure (x : α) : evalDist (pure x : OracleComp spec α) = PMF.pure (some x) := rfl

@[simp]
lemma evalDist_query (i : ι) (t : spec.domain i) :
    evalDist (query i t) = (PMF.uniformOfFintype (spec.range i)).map some := by
  simp [query_def, -queryBind'_eq_queryBind, evalDist, evalDistT, PMF.map,
    OracleComp.mapM, OptionT.lift, PMF.monad_map_eq_map]

@[simp]
lemma evalDist_failure : evalDist (failure : OracleComp spec α) = PMF.pure none := rfl

@[simp]
lemma evalDist_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    evalDist (oa >>= ob) = (evalDist oa).bind (Option.rec (PMF.pure none) (evalDist ∘ ob)) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp only [pure_bind, evalDist_pure, PMF.pure_bind, Function.comp_apply]
  | query_bind i t oa hoa => sorry --simp [← queryBind'_eq_queryBind, evalDist, hoa]
  | failure => simp only [failure_bind, evalDist_failure, PMF.pure_bind]

lemma evalDist_query_bind (i : ι) (t : spec.domain i) (ou : spec.range i → OracleComp spec α) :
    evalDist (query i t >>= ou) = (PMF.uniformOfFintype (spec.range i)).bind (evalDist ∘ ou) := by
  sorry

@[simp]
lemma evalDist_map (oa : OracleComp spec α) (f : α → β) :
    evalDist (f <$> oa) = (evalDist oa).map (Option.map f) := by
  rw [map_eq_bind_pure_comp, evalDist_bind, PMF.map]
  refine congr_arg (oa.evalDist.bind ·) (funext λ x ↦ ?_)
  cases x <;> simp

@[simp]
lemma evalDist_seq (oa : OracleComp spec α) (og : OracleComp spec (α → β)) : evalDist (og <*> oa) =
    (evalDist og).bind (Option.rec (PMF.pure none) λ f ↦ (evalDist oa).map (Option.map f)) := by
  rw [seq_eq_bind_map, evalDist_bind]
  refine congr_arg (evalDist og).bind (funext λ mf ↦ ?_)
  cases mf
  · rfl
  · simp only [Function.comp_apply, evalDist_map]

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
noncomputable def probOutput (oa : OracleComp spec α) (x : α) : ℝ≥0∞ :=
  evalDist oa (some x)

notation "[=" x "|" oa "]" => probOutput oa x

lemma probOutput_def (oa : OracleComp spec α) (x : α) :
    [= x | oa] = evalDist oa (some x) := rfl

lemma evalDist_apply_some (oa : OracleComp spec α) (x : α) :
    evalDist oa (some x) = [= x | oa] := rfl

@[simp]
lemma evalDist_comp_some (oa : OracleComp spec α) :
    evalDist oa ∘ some = ([= · | oa]) := rfl

/-- `[⊥ | oa]` is the probability of the computation `oa` failing. -/
noncomputable def probFailure (oa : OracleComp spec α) : ℝ≥0∞ :=
  evalDist oa none

notation "[⊥" "|" oa "]" => probFailure oa

lemma probFailure_def (oa : OracleComp spec α) :
    [⊥ | oa] = evalDist oa none := rfl

lemma evalDist_apply_none (oa : OracleComp spec α) :
    evalDist oa none = [⊥ | oa] := rfl

/-- `[p | oa]` is the probability of getting a result that satisfies a predicate `p`
after running the computation `oa`, assuming all oracles respond uniformly at random.-/
noncomputable def probEvent (oa : OracleComp spec α) (p : α → Prop) : ℝ≥0∞ :=
  (evalDist oa).toOuterMeasure (Option.some '' {x | p x})

notation "[" p "|" oa "]" => probEvent oa p

lemma probEvent_def (oa : OracleComp spec α) (p : α → Prop) :
    [p | oa] = (evalDist oa).toOuterMeasure (Option.some '' {x | p x}) := rfl

lemma probEvent_eq_tsum_indicator (oa : OracleComp spec α) (p : α → Prop) :
    [p | oa] = ∑' x : α, {x | p x}.indicator ([= · | oa]) x := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, Set.indicator_image (Option.some_injective _),
    tsum_option _ ENNReal.summable]

/-- More explicit form of `probEvent_eq_tsum_indicator` when the predicate `p` is decidable. -/
lemma probEvent_eq_tsum_ite (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    [p | oa] = ∑' x : α, if p x then [= x | oa] else 0 := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, tsum_option _ ENNReal.summable,
    Set.indicator, probOutput_def]

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

variable {oa : OracleComp spec α} {x : α} {p : α → Prop}

@[simp] lemma probOutput_le_one : [= x | oa] ≤ 1 := PMF.coe_le_one (evalDist oa) x
@[simp] lemma probFailure_le_one : [⊥ | oa] ≤ 1 := PMF.coe_le_one (evalDist oa) none

@[simp] lemma tsum_probOutput_le_one : ∑' x : α, [= x | oa] ≤ 1 :=
  le_of_le_of_eq (le_add_self) (probFailure_add_tsum_probOutput oa)
@[simp] lemma probEvent_le_one : [p | oa] ≤ 1 := by
  rw [probEvent_def, PMF.toOuterMeasure_apply]
  refine le_of_le_of_eq (ENNReal.tsum_le_tsum λ x ↦ ?_) (oa.evalDist.tsum_coe)
  exact Set.indicator_le_self (some '' {x | p x}) (oa.evalDist) x

@[simp] lemma probOutput_ne_top : [= x | oa] ≠ ∞ := PMF.apply_ne_top (evalDist oa) x
@[simp] lemma probOutput_lt_top : [= x | oa] < ∞ := PMF.apply_lt_top (evalDist oa) x
@[simp] lemma not_one_lt_probOutput : ¬ 1 < [= x | oa] := not_lt.2 probOutput_le_one

@[simp] lemma probEvent_ne_top : [p | oa] ≠ ∞ := ne_top_of_le_ne_top one_ne_top probEvent_le_one
@[simp] lemma probEvent_lt_top : [p | oa] < ∞ := lt_top_iff_ne_top.2 probEvent_ne_top
@[simp] lemma not_one_lt_probEvent : ¬ 1 < [p | oa] := not_lt.2 probEvent_le_one

@[simp] lemma probFailure_ne_top : [⊥ | oa] ≠ ∞ := PMF.apply_ne_top (evalDist oa) none
@[simp] lemma probFailure_lt_top : [⊥ | oa] < ∞ := PMF.apply_lt_top (evalDist oa) none
@[simp] lemma not_one_lt_probFailure : ¬ 1 < [⊥ | oa] := not_lt.2 probFailure_le_one

@[simp] lemma one_le_probOutput_iff : 1 ≤ [= x | oa] ↔ [= x | oa] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probOutput, or_false, eq_comm]
@[simp] lemma one_le_probEvent_iff : 1 ≤ [p | oa] ↔ [p | oa] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probEvent, or_false, eq_comm]
@[simp] lemma one_le_probFailure_iff : 1 ≤ [⊥ | oa] ↔ [⊥ | oa] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probFailure, or_false, eq_comm]

end bounds

lemma tsum_probOutput_eq_sub (oa : OracleComp spec α) :
    ∑' x, [= x | oa] = 1 - [⊥ | oa] := by
  refine ENNReal.eq_sub_of_add_eq probFailure_ne_top (tsum_probOutput_add_probFailure oa)

lemma sum_probOutput_eq_sub [Fintype α] (oa : OracleComp spec α) :
    ∑ x, [= x | oa] = 1 - [⊥ | oa] := by
  rw [← tsum_fintype, tsum_probOutput_eq_sub]

lemma probFailure_eq_sub_tsum (oa : OracleComp spec α) :
    [⊥ | oa] = 1 - ∑' x, [= x | oa] := by
  refine ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
    (probFailure_add_tsum_probOutput oa)

lemma probFailure_eq_sub_sum [Fintype α] (oa : OracleComp spec α) :
    [⊥ | oa] = 1 - ∑ x, [= x | oa] := by
  rw [← tsum_fintype, probFailure_eq_sub_tsum]

lemma tsum_probOutput_eq_one (oa : OracleComp spec α) (h : [⊥ | oa] = 0) :
    ∑' x, [= x | oa] = 1 := by
  rw [tsum_probOutput_eq_sub, h, tsub_zero]

lemma sum_probOutput_eq_one [Fintype α] (oa : OracleComp spec α) (h : [⊥ | oa] = 0) :
    ∑ x, [= x | oa] = 1 := by
  rw [sum_probOutput_eq_sub, h, tsub_zero]

section support

variable (oa : OracleComp spec α) (x : α) (p q : α → Prop)

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
@[simp low]
lemma zero_eq_probOutput_iff : 0 = [= x | oa] ↔ x ∉ oa.support := by
  rw [eq_comm, probOutput_eq_zero_iff]
alias ⟨_, zero_eq_probOutput⟩ := zero_eq_probOutput_iff

@[simp]
lemma probOutput_eq_zero_iff' [DecidableEq α] : [= x | oa] = 0 ↔ x ∉ oa.finSupport := by
  rw [mem_finSupport_iff_mem_support, probOutput_eq_zero_iff]
alias ⟨not_mem_fin_support_of_probOutput_eq_zero, probOutput_eq_zero'⟩ := probOutput_eq_zero_iff
@[simp]
lemma zero_eq_probOutput_iff' [DecidableEq α] : 0 = [= x | oa] ↔ x ∉ oa.finSupport := by
  rw [eq_comm, probOutput_eq_zero_iff']
alias ⟨_, zero_eq_probOutput'⟩ := zero_eq_probOutput_iff'

@[simp low]
lemma probEvent_eq_zero_iff : [p | oa] = 0 ↔ ∀ x ∈ oa.support, ¬ p x := by
  rw [probEvent_def, PMF.toOuterMeasure_apply_eq_zero_iff]
  simp [Set.disjoint_iff_forall_ne, Option.forall]
  refine forall_congr' λ x ↦ forall_congr' λ hx ↦ ?_
  refine ⟨λ h hx ↦ h x hx rfl, λ h y hy hxy ↦ h (hxy ▸ hy)⟩
alias ⟨not_of_mem_support_of_probEvent_eq_zero, probEvent_eq_zero⟩ := probEvent_eq_zero_iff
@[simp low]
lemma zero_eq_probEvent_iff : 0 = [p | oa] ↔ ∀ x ∈ oa.support, ¬ p x := by
  rw [eq_comm, probEvent_eq_zero_iff]
alias ⟨_, zero_eq_probEvent⟩ := zero_eq_probEvent_iff

@[simp]
lemma probEvent_eq_zero_iff' [DecidableEq α] : [p | oa] = 0 ↔ ∀ x ∈ oa.finSupport, ¬ p x := by
  simp only [probEvent_eq_zero_iff, mem_finSupport_iff_mem_support]
alias ⟨not_of_mem_finSupport_of_probEvent_eq_zero, probEvent_eq_zero'⟩ := probEvent_eq_zero_iff'
@[simp]
lemma zero_eq_probEvent_iff' [DecidableEq α] : 0 = [p | oa] ↔ ∀ x ∈ oa.finSupport, ¬ p x := by
  rw [eq_comm, probEvent_eq_zero_iff']
alias ⟨_, zero_eq_probEvent'⟩ := zero_eq_probEvent_iff'

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
@[simp low]
lemma one_eq_probOutput_iff :
    1 = [= x | oa] ↔ [⊥ | oa] = 0 ∧ oa.support = {x} := by
  rw [eq_comm, probOutput_eq_one_iff]
alias ⟨_, one_eq_probOutput⟩ := one_eq_probOutput_iff

@[simp]
lemma probOutput_eq_one_iff' [DecidableEq α] :
    [= x | oa] = 1 ↔ [⊥ | oa] = 0 ∧ oa.finSupport = {x} := by
  rw [probOutput_eq_one_iff, finSupport_eq_iff_support_eq_coe, Finset.coe_singleton]
alias ⟨_, probOutput_eq_one'⟩ := probOutput_eq_one_iff'
@[simp]
lemma one_eq_probOutput_iff' [DecidableEq α] :
    1 = [= x | oa] ↔ [⊥ | oa] = 0 ∧ oa.finSupport = {x} := by
  rw [eq_comm, probOutput_eq_one_iff']
alias ⟨_, one_eq_probOutput'⟩ := one_eq_probOutput_iff'

@[simp low]
lemma probEvent_eq_one_iff : [p | oa] = 1 ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.support, p x := by
  rw [probEvent, PMF.toOuterMeasure_apply_eq_one_iff]
  simp [support_evalDist]
  split_ifs with hoa
  · simp [hoa, Set.preimage_image_eq _ (some_injective α), Set.subset_def]
  · simp [hoa]
    intro h
    specialize h (Set.mem_insert none _)
    simp at h
alias ⟨_, probEvent_eq_one⟩ := probEvent_eq_one_iff
@[simp low]
lemma one_eq_probEvent_iff : 1 = [p | oa] ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.support, p x := by
  rw [eq_comm, probEvent_eq_one_iff]
alias ⟨_, one_eq_probEvent⟩ := probEvent_eq_one_iff

@[simp]
lemma probEvent_eq_one_iff' [DecidableEq α] :
    [p | oa] = 1 ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.finSupport, p x := by
  simp_rw [probEvent_eq_one_iff, mem_finSupport_iff_mem_support]
alias ⟨_, probEvent_eq_one'⟩ := probEvent_eq_one_iff'
@[simp]
lemma one_eq_probEvent_iff' [DecidableEq α] :
    1 = [p | oa] ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.finSupport, p x := by
  rw [eq_comm, probEvent_eq_one_iff']
alias ⟨_, one_eq_probEvent'⟩ := one_eq_probEvent_iff'

lemma mem_support_iff_probOutput_ne_zero : x ∈ oa.support ↔ [= x | oa] ≠ 0 := by
  simp only [ne_eq, probOutput_eq_zero_iff, not_not]
lemma mem_finSupport_iff_probOutput_ne_zero [DecidableEq α] :
    x ∈ oa.finSupport ↔ [= x | oa] ≠ 0 := by
  rw [mem_finSupport_iff_mem_support, mem_support_iff_probOutput_ne_zero]

lemma mem_support_iff_probOutput_pos : x ∈ oa.support ↔ 0 < [= x | oa] := by
  simp only [probOutput_pos_iff]

lemma not_mem_support_iff_probOutput_eq_zero : x ∉ oa.support ↔ [= x | oa] = 0 := by
  simp only [probOutput_eq_zero_iff]

variable {oa x p q}

/-- If `p` implies `q` on the `support` of a computation then it is more likely to happen. -/
lemma probEvent_mono (h : ∀ x ∈ oa.support, p x → q x) : [p | oa] ≤ [q | oa] := by
  refine PMF.toOuterMeasure_mono _ λ x hx ↦ match x with
  | none => by simp at hx
  | some x => by
      simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, some.injEq, exists_eq_right,
        PMF.mem_support_iff, ne_eq, evalDist_apply_eq_zero_iff, not_not] at hx
      exact ⟨x, h x hx.2 hx.1, rfl⟩

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

@[simp] lemma probEvent_eq_eq_probOutput (oa : OracleComp spec α) (x : α) :
    [(· = x) | oa] = [= x | oa] := by
  simp [probEvent_def, PMF.toOuterMeasure_apply_singleton, evalDist_apply_some]

@[simp] lemma probEvent_eq_eq_probOutput' (oa : OracleComp spec α) (x : α) :
    [(x = ·) | oa] = [= x | oa] :=
  (probEvent_congr (λ _ ↦ eq_comm) rfl).trans (probEvent_eq_eq_probOutput oa x)

section sums

variable (oa : OracleComp spec α) (p : α → Prop)

/-- The probability of an event written as a sum over the set `{x | p x}` viewed as a subtype.
This notably doesn't require decidability of the predicate `p` unlike many other lemmas. -/
lemma probEvent_eq_tsum_subtype : [p | oa] = ∑' x : {x | p x}, [= x | oa] := by
  rw [probEvent_eq_tsum_indicator, tsum_subtype]

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

lemma probEvent_eq_tsum_subtype_support_ite [DecidablePred p] :
    [p | oa] = ∑' x : oa.support, if p x then [= x | oa] else 0 :=
calc
  [p | oa] = (∑' x, if p x then [= x | oa] else 0) := by rw [probEvent_eq_tsum_ite oa p]
  _ = ∑' x, oa.support.indicator (λ x ↦ if p x then [= x | oa] else 0) x := by
    refine tsum_congr (λ x ↦ ?_)
    unfold Set.indicator
    split_ifs with h1 h2 h2 <;> simp [h1, h2]
  _ = ∑' x : oa.support, if p x then [= x | oa] else 0 := by
    rw [tsum_subtype (support oa) (λ x ↦ if p x then [= x | oa] else 0)]

lemma probEvent_eq_sum_fintype_indicator [Fintype α] (oa : OracleComp spec α) (p : α → Prop) :
    [p | oa] = ∑ x : α, {x | p x}.indicator ([= · | oa]) x :=
  (probEvent_eq_tsum_indicator oa p).trans (tsum_fintype _)

lemma probEvent_eq_sum_fintype_ite [DecidablePred p] [Fintype α] :
    [p | oa] = ∑ x : α, if p x then [= x | oa] else 0 :=
  (probEvent_eq_tsum_ite oa p).trans (tsum_fintype _)

lemma probEvent_eq_sum_filter_univ [DecidablePred p] [Fintype α] :
    [p | oa] = ∑ x in Finset.univ.filter p, [= x | oa] := by
  rw [probEvent_eq_sum_fintype_ite, Finset.sum_filter]

lemma probEvent_eq_sum_filter_finSupport [DecidablePred p] [DecidableEq α] :
    [p | oa] = ∑ x in oa.finSupport.filter p, [= x | oa] :=
  (probEvent_eq_tsum_ite oa p).trans <|
    (tsum_eq_sum' <| by simp; tauto).trans
      (Finset.sum_congr rfl <| λ x hx ↦ if_pos (Finset.mem_filter.1 hx).2)

lemma probEvent_eq_sum_finSupport_ite [DecidablePred p] [DecidableEq α] :
    [p | oa] = ∑ x in oa.finSupport, if p x then [= x | oa] else 0 := by
  rw [probEvent_eq_sum_filter_finSupport, Finset.sum_filter]

end sums

lemma probOutput_congr {x y : α} {oa oa' : OracleComp spec α}
    (h1 : x = y) (h2 : evalDist oa = evalDist oa') : [= x | oa] = [= y | oa'] := by
  simp_rw [probOutput, h1, h2]

lemma probEvent_congr' {p q : α → Prop} {oa oa' : OracleComp spec α}
    (h1 : ∀ x, x ∈ oa.support → x ∈ oa'.support → (p x ↔ q x))
    (h2 : evalDist oa = evalDist oa') : [p | oa] = [q | oa'] := by
  have : DecidablePred q := Classical.decPred q
  have h : ∀ x, x ∈ oa.support ↔ x ∈ oa'.support := mem_support_iff_of_evalDist_eq h2
  have h' : ∀ x, [= x | oa] = [= x | oa'] := λ x ↦ probOutput_congr rfl h2
  rw [probEvent_eq_tsum_indicator, probEvent_eq_tsum_indicator]
  refine tsum_congr λ x ↦ ?_
  simp [Set.indicator, h']
  by_cases hp : p x
  · by_cases hq : q x
    · simp [hp, hq]
    · simp [hp, hq, h]
      refine λ hoa ↦ hq ?_
      refine (h1 _ ?_ hoa).1 hp
      refine (h _).2 hoa
  · by_cases hq : q x
    · simp [hp, hq]
      simp [h] at h1
      intro hoa
      specialize h1 _ hoa
      tauto
    · rw [if_neg hp, if_neg hq]


@[simp] lemma probEvent_const (oa : OracleComp spec α) (p : Prop) [Decidable p] :
    [λ _ ↦ p | oa] = if p then 1 - [⊥ | oa] else 0 := by
  rw [probEvent_eq_tsum_ite]
  split_ifs with hp <;> simp [hp, tsum_probOutput_eq_sub]

lemma probEvent_true (oa : OracleComp spec α) : [λ _ ↦ true | oa] = 1 - [⊥ | oa] := by simp
lemma probEvent_false (oa : OracleComp spec α) : [λ _ ↦ false | oa] = 0 := by simp

lemma probFailure_eq_sub_probEvent (oa : OracleComp spec α) :
    [⊥ | oa] = 1 - [λ _ ↦ true | oa] := by
  rw [probEvent_true, ENNReal.sub_sub_cancel one_ne_top probFailure_le_one]

lemma evalDist_ext_probEvent {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h : ∀ x, [= x | oa] = [= x | oa']) : evalDist oa = evalDist oa' :=
  PMF.ext λ x ↦ match x with
  | none => by simp [← probFailure_def, probFailure_eq_sub_tsum, h]
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
  simp [probEvent_eq_tsum_ite]
  refine (tsum_eq_single x (by simp; tauto)).trans (by simp)

lemma probEvent_pure_eq_zero {p : α → Prop} {x : α} (h : ¬ p x) :
    [p | (pure x : OracleComp spec α)] = 0 := by simpa

lemma probEvent_pure_eq_one {p : α → Prop} {x : α} (h : p x) :
    [p | (pure x : OracleComp spec α)] = 1 := by simpa

end pure

section bind

variable (oa : OracleComp spec α) (ob : α → OracleComp spec β)

lemma probOutput_bind_eq_tsum (y : β) :
    [= y | oa >>= ob] = ∑' x : α, [= x | oa] * [= y | ob x] := by
  simp [probOutput, evalDist_bind, tsum_option _ ENNReal.summable]

lemma probFailure_bind_eq_tsum :
    [⊥ | oa >>= ob] = [⊥ | oa] + ∑' x : α, [= x | oa] * [⊥ | ob x] := by
  simp [probFailure, evalDist_bind, tsum_option _ ENNReal.summable, ← probOutput_def]

lemma probEvent_bind_eq_tsum (q : β → Prop) :
    [q | oa >>= ob] = ∑' x : α, [= x | oa] * [q | ob x] := by
  simp [probEvent_def, evalDist_bind, PMF.toOuterMeasure_bind_apply,
    tsum_option _ ENNReal.summable, evalDist_apply_some]

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
  (probOutput_bind_eq_tsum oa ob y).trans (tsum_fintype _)

lemma probFailure_bind_eq_sum_fintype [Fintype α] :
    [⊥ | oa >>= ob] = [⊥ | oa] + ∑ x : α, [= x | oa] * [⊥ | ob x] :=
  (probFailure_bind_eq_tsum oa ob).trans (congr_arg ([⊥ | oa] + ·) <| tsum_fintype _)

lemma probEvent_bind_eq_sum_fintype [Fintype α] (q : β → Prop) [DecidablePred q] :
    [q | oa >>= ob] = ∑ x : α, [= x | oa] * [q | ob x] :=
  (probEvent_bind_eq_tsum oa ob q).trans (tsum_fintype _)

lemma probOutput_bind_eq_sum_finSupport [DecidableEq α] (y : β) :
    [= y | oa >>= ob] = ∑ x in oa.finSupport, [= x | oa] * [= y | ob x] :=
  (probOutput_bind_eq_tsum oa ob y).trans (tsum_eq_sum' <| by simp)

lemma probEvent_bind_eq_sum_finSupport [DecidableEq α] (q : β → Prop) [DecidablePred q] :
    [q | oa >>= ob] = ∑ x in oa.finSupport, [= x | oa] * [q | ob x] :=
  (probEvent_bind_eq_tsum oa ob q).trans (tsum_eq_sum' <| by simp)

lemma probOutput_bind_of_const (y : β) (r : ℝ≥0∞) (h : ∀ x, [= y | ob x] = r) :
    [= y | oa >>= ob] = (1 - [⊥ | oa]) * r := by
  simp [probOutput_bind_eq_tsum, h, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub]

lemma probFailure_bind_of_const [Nonempty α] (r : ℝ≥0∞) (h : ∀ x, [⊥ | ob x] = r) :
    [⊥ | oa >>= ob] = [⊥ | oa] + r - [⊥ | oa] * r := by
  have : r ≠ ⊤ := λ hr ↦ probFailure_ne_top ((h (Classical.arbitrary α)).trans hr)
  simp [probFailure_bind_eq_tsum, h, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub]
  rw [ENNReal.sub_mul λ _ _ ↦ this, one_mul]
  refine symm (AddLECancellable.add_tsub_assoc_of_le ?_ ?_ _)
  · refine ENNReal.addLECancellable_iff_ne.2 (ENNReal.mul_ne_top probFailure_ne_top this)
  · by_cases hr : r = 0
    · simp only [hr, mul_zero, le_refl]
    refine mul_le_of_le_div (le_of_le_of_eq probFailure_le_one ?_)
    refine symm (ENNReal.div_self hr this)

end bind

section bind_const

variable (oa : OracleComp spec α) (ob : OracleComp spec β)

-- lemma probFailure_bind_const :
--   [⊥ | do oa; ob] = [⊥ | oa] + [⊥ | ob] - [⊥ | oa] * [⊥ | ob]


end bind_const

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
  simp only [probEvent, evalDist_map, PMF.toOuterMeasure_map_apply, Function.comp_apply]
  refine congr_arg (oa.evalDist.toOuterMeasure) ?_
  simp only [Set.preimage, Set.mem_image, Set.mem_setOf_eq, Set.ext_iff]
  intro x
  cases x <;> simp
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

@[simp] lemma probFailure_eqRec : [⊥ | h ▸ oa] = [⊥ | oa] := by induction h; rfl

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
