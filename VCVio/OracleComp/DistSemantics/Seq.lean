/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist
import ToMathlib.General

/-!
# Lemmas About the Distribution Semantics of Seq

This file collects various lemmas about the monadic sequence operation `og <*> oa`.

One especially important case is `f <$> oa <*> ob` where `f : α → β → γ`,
that runs the two computations `oa` and `ob` to get some `x` and `y` respectively,
returning only the value `f x y`.
-/

open Mathlib OracleSpec ENNReal BigOperators

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β γ : Type}

section basic

variable (oa : OracleComp spec α) (og : OracleComp spec (α → β))

@[simp low]
lemma support_seq : (og <*> oa).support = ⋃ g ∈ og.support, g '' oa.support := by
  simp [seq_eq_bind_map]

@[simp low]
lemma finSupport_seq [DecidableEq α] [DecidableEq β] [DecidableEq (α → β)] :
    (og <*> oa).finSupport = og.finSupport.biUnion (λ g ↦ oa.finSupport.image g) := by
  simp [seq_eq_bind_map]

@[simp]
lemma evalDist_seq : evalDist (og <*> oa) = (evalDist og).seq (evalDist oa) := by
  simp [PMF.ext_iff, seq_eq_bind_map, ← ENNReal.tsum_mul_left]

lemma probOutput_seq_eq_tsum (y : β) : [= y | og <*> oa] =
    ∑' g, ∑' x, [= g | og] * [= x | oa] * [= y | (pure (g x) : OracleComp spec β)] := by
  simp [seq_eq_bind, probOutput_bind_eq_tsum, probOutput_map_eq_tsum,
    ← ENNReal.tsum_mul_left, mul_assoc]

lemma probOutput_seq_eq_tsum_ite [DecidableEq β] (y : β) : [= y | og <*> oa] =
    ∑' g, ∑' x, if y = g x then [= g | og] * [= x | oa] else 0 := by
  simp [seq_eq_bind, probOutput_bind_eq_tsum,
    probOutput_map_eq_tsum_ite, ← ENNReal.tsum_mul_left]

lemma probOutput_seq_eq_sum_finSupport_ite [DecidableEq α] [DecidableEq (α → β)] [DecidableEq β]
    (y : β) : [= y | og <*> oa] = ∑ g in og.finSupport, ∑ x in oa.finSupport,
      if y = g x then [= g | og] * [= x | oa] else 0 := by
  simp [seq_eq_bind, probOutput_bind_eq_sum_finSupport,
    probOutput_map_eq_sum_finSupport_ite, Finset.mul_sum]

lemma probEvent_seq_eq_tsum (p : β → Prop) :
    [p | og <*> oa] = ∑' (g : α → β), [= g | og] * [p ∘ g | oa] := by
  simp only [seq_eq_bind, probEvent_bind_eq_tsum, probEvent_map]

lemma probEvent_seq_eq_tsum_ite (p : β → Prop) [DecidablePred p] :
    [p | og <*> oa] = ∑' (g : α → β) (x : α),
      if p (g x) then [= g | og] * [= x | oa] else 0 := by
  simp_rw [probEvent_seq_eq_tsum, probEvent_eq_tsum_ite, Function.comp_apply,
    ← ENNReal.tsum_mul_left, mul_ite, mul_zero]

end basic

-- lemma evalDist_seq_congr_ext {oa oa' : OracleComp spec α} {og og' : OracleComp spec (α → β)}
--     (h1 : evalDist oa = evalDist oa')
--     (h2 : ∀ x ∈ oa.support, evalDist ((· x) <$> og) = evalDist ((· x) <$> og')) :
--     evalDist (og <*> oa) = evalDist (og' <*> oa'):= by
--   sorry

section seq_map

variable (oa : OracleComp spec α) (ob : OracleComp spec β) (f : α → β → γ)

@[simp low + 1]
lemma support_seq_map_eq_image2 :
    (f <$> oa <*> ob).support = Set.image2 f oa.support ob.support := by
  simp only [support_seq, support_map, Set.mem_image, Set.iUnion_exists, Set.biUnion_and',
    Set.iUnion_iUnion_eq_right, Set.ext_iff, Set.mem_iUnion, exists_prop, Set.mem_image2,
    implies_true]

@[simp low + 1]
lemma finSupport_seq_map_eq_image2 [DecidableEq α] [DecidableEq β] [DecidableEq γ] :
    (f <$> oa <*> ob).finSupport = Finset.image₂ f oa.finSupport ob.finSupport := by
  simp only [finSupport_eq_iff_support_eq_coe, support_seq, support_map, Set.mem_image,
    Set.iUnion_exists, Set.biUnion_and', Set.iUnion_iUnion_eq_right, Finset.coe_image₂,
    coe_finSupport, Set.ext_iff, Set.mem_iUnion, exists_prop, Set.mem_image2, implies_true]

lemma evalDist_seq_map : evalDist (f <$> oa <*> ob) = ((evalDist oa).map f).seq (evalDist ob) := by
  rw [evalDist_seq, evalDist_map]

lemma probOutput_seq_map_eq_tsum (z : γ) : [= z | f <$> oa <*> ob] =
    ∑' (x : α) (y : β), [= x | oa] * [= y | ob] * [= z | (pure (f x y) : OracleComp spec γ)] := by
  simp only [map_eq_bind_pure_comp, Function.comp, seq_eq_bind, bind_assoc, pure_bind,
    probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left, mul_assoc]

lemma probOutput_seq_map_eq_tsum_ite [DecidableEq γ] (z : γ) : [= z | f <$> oa <*> ob] =
    ∑' (x : α) (y : β), if z = f x y then [= x | oa] * [= y | ob] else 0 := by
  simp only [probOutput_seq_map_eq_tsum, probOutput_pure, mul_ite, mul_one, mul_zero]

-- @[simp] lemma prob_output_seq_map_eq_sum [decidable_eq α] [decidable_eq β]
--   [decidable_eq γ] (z : γ) : ⁅= z | f <$> oa <*> ob⁆ = ∑ x in oa.fin_support,
--     ∑ y in ob.fin_support, if z = f x y then ⁅= x | oa⁆ * ⁅= y | ob⁆ else 0 :=
-- by simp_rw [seq_map_eq_bind_bind, prob_output_bind_eq_sum, finset.mul_sum,
--   prob_output_return, mul_ite, mul_one, mul_zero]

-- @[simp] lemma prob_event_seq_map_eq_tsum (p : γ → Prop) [decidable_pred p] :
--   ⁅p | f <$> oa <*> ob⁆ = ∑' x y, if p (f x y) then ⁅= x | oa⁆ * ⁅= y | ob⁆ else 0 :=
-- by simp_rw [seq_map_eq_bind_bind, prob_event_bind_eq_tsum, ← ennreal.tsum_mul_left,
--   prob_event_return, mul_ite, mul_one, mul_zero]

-- @[simp] lemma prob_event_seq_map_eq_sum [decidable_eq α] [decidable_eq β]
--   (p : γ → Prop) [decidable_pred p] : ⁅p | f <$> oa <*> ob⁆ = ∑ x in oa.fin_support,
--     ∑ y in ob.fin_support, if p (f x y) then ⁅= x | oa⁆ * ⁅= y | ob⁆ else 0 :=
-- by simp_rw [seq_map_eq_bind_bind, prob_event_bind_eq_sum, finset.mul_sum,
--   prob_event_return, mul_ite, mul_one, mul_zero]

lemma probEvent_seq_map_eq_probEvent_comp_uncurry (p : γ → Prop) :
    [p | f <$> oa <*> ob] = [p ∘ f.uncurry | (·, ·) <$> oa <*> ob] := by
  rw [probEvent_comp]
  refine probEvent_congr' ?_ (congr_arg evalDist ?_)
  · simp only [support_seq_map_eq_image2, Set.mem_image2, support_map, Set.image2_mk_eq_prod,
      Set.image_uncurry_prod, implies_true]
  · simp only [map_seq, Function.comp, Functor.map_map, Function.uncurry_apply_pair]

lemma probEvent_seq_map_eq_probEvent (p : γ → Prop) :
    [p | f <$> oa <*> ob] = [λ x ↦ p (f x.1 x.2) | (·, ·) <$> oa <*> ob] :=
  probEvent_seq_map_eq_probEvent_comp_uncurry oa ob f p

section swap

@[simp]
lemma probOutput_seq_map_swap (z : γ) :
    [= z | Function.swap f <$> ob <*> oa] = [= z | f <$> oa <*> ob] := by
  simp [probOutput_seq_map_eq_tsum, Function.swap]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (λ x ↦ tsum_congr (λ y ↦ ?_))
  rw [mul_comm [= x | oa]]

@[simp]
lemma evalDist_seq_map_swap :
    evalDist (Function.swap f <$> ob <*> oa) = evalDist (f <$> oa <*> ob) :=
  evalDist_ext_probEvent (probOutput_seq_map_swap oa ob f)

@[simp]
lemma probEvent_seq_map_swap (p : γ → Prop) :
    [p | Function.swap f <$> ob <*> oa] = [p | f <$> oa <*> ob] :=
  probEvent_congr (evalDist_seq_map_swap oa ob f)

@[simp]
lemma support_seq_map_swap : (Function.swap f <$> ob <*> oa).support = (f <$> oa <*> ob).support :=
  Set.ext (mem_support_iff_of_evalDist_eq (evalDist_seq_map_swap oa ob f))

@[simp]
lemma finSupport_seq_map_swap [DecidableEq γ] :
    (Function.swap f <$> ob <*> oa).finSupport = (f <$> oa <*> ob).finSupport :=
  Finset.ext (mem_finSupport_iff_of_evalDist_eq (evalDist_seq_map_swap oa ob f))

end swap

section injective2

lemma mem_support_seq_map_iff_of_injective2 (hf : f.Injective2) (x : α) (y : β) :
    f x y ∈ (f <$> oa <*> ob).support ↔ x ∈ oa.support ∧ y ∈ ob.support := by
  rw [support_seq_map_eq_image2, Set.mem_image2_iff hf]

lemma mem_finSupport_seq_map_iff_of_injective2 [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (hf : f.Injective2) (x : α) (y : β) : f x y ∈ (f <$> oa <*> ob).finSupport ↔
      x ∈ oa.finSupport ∧ y ∈ ob.finSupport := by
  simp_rw [mem_finSupport_iff_mem_support, mem_support_seq_map_iff_of_injective2 oa ob f hf]

lemma probOutput_seq_map_eq_mul_of_injective2 (hf : f.Injective2) (x : α) (y : β) :
    [= f x y | f <$> oa <*> ob] = [= x | oa] * [= y | ob] := by
  rw [probOutput_seq_map_eq_tsum]
  rw [← ENNReal.tsum_prod]
  refine (tsum_eq_single (x, y) (λ (x', y') h ↦ ?_)).trans ?_
  · suffices f x y ≠ f x' y' by simp [this]
    exact λ h' ↦ h (Prod.eq_iff_fst_eq_snd_eq.2 (hf h'.symm))
  · rw [probOutput_pure_self, mul_one]

end injective2

/-- If the results of the computations `oa` and `ob` are combined with some function `f`,
and there exists unique `x` and `y` such that `f x y = z` (given as explicit arguments),
then the probability of getting `z` as an output of `f <$> oa <*> ob`
is the product of probabilities of getting `x` and `y` from `oa` and `ob` respectively. -/
lemma probOutput_seq_map_eq_mul (x : α) (y : β) (z : γ)
    (h : ∀ x' ∈ oa.support, ∀ y' ∈ ob.support, z = f x' y' ↔ x' = x ∧ y' = y) :
    [= z | f <$> oa <*> ob] = [= x | oa] * [= y | ob] := by
  have : DecidableEq γ := Classical.decEq γ
  rw [probOutput_seq_map_eq_tsum_ite, ← ENNReal.tsum_prod]
  refine (tsum_eq_single (x, y) (λ (x', y') ↦ ?_)).trans ?_
  · simp only [ne_eq, Prod.mk.injEq, ite_eq_right_iff, mul_eq_zero,
      probOutput_eq_zero_iff, ← not_and_or]
    exact λ h1 h2 h3 ↦ h1 ((h x' h3.1 y' h3.2).1 h2)
  · simp only [ite_eq_left_iff, zero_eq_mul, probOutput_eq_zero_iff, ← not_and_or]
    intro h1 h2
    refine h1 ((h x h2.1 y h2.2).2 ⟨rfl, rfl⟩)

/-- If the results of the computations `oa` and `ob` are combined with some function `f`,
and `p` is an event such that outputs of `f` are in `p` iff the individual components
lie in some other events `q1` and `q2`, then the probability of the event `p` is the
product of the probabilites holding individually. -/
lemma probEvent_seq_map_eq_mul (p : γ → Prop) (q1 : α → Prop) (q2 : β → Prop)
    (h : ∀ x ∈ oa.support, ∀ y ∈ ob.support, p (f x y) ↔ q1 x ∧ q2 y) :
    [p | f <$> oa <*> ob] = [q1 | oa] * [q2 | ob] := by
  have : DecidablePred p := Classical.decPred p
  have : DecidablePred q1 := Classical.decPred q1
  have : DecidablePred q2 := Classical.decPred q2
  rw [probEvent_seq_map_eq_probEvent]
  calc [λ (x, y) ↦ p (f x y) | (·, ·) <$> oa <*> ob] =
      [λ (x, y) ↦ q1 x ∧ q2 y | (·, ·) <$> oa <*> ob] :=
        probEvent_ext <| by simpa using λ x y hx hy ↦ h x hx y hy
    _ = ∑' (x : α) (y : β), if q1 x ∧ q2 y then [= (x, y) | (·, ·) <$> oa <*> ob] else 0 := by
      rw [probEvent_eq_tsum_ite, ENNReal.tsum_prod']
    _ = ∑' (x : α) (y : β), if q1 x ∧ q2 y then [= x | oa] * [= y | ob] else 0 := by
      simp_rw [probOutput_seq_map_eq_mul_of_injective2 oa ob Prod.mk Prod.mk.injective2]
    _ = ∑' x : α, if q1 x then [= x | oa] * (∑' y : β, if q2 y then [= y | ob] else 0) else 0 :=
      tsum_congr (λ x ↦ by by_cases hx : q1 x <;> simp [hx, ← ENNReal.tsum_mul_left])
    _ = ∑' x : α, if q1 x then [= x | oa] * [q2 | ob] else 0 := by rw [probEvent_eq_tsum_ite]
    _ = [q1 | oa] * [q2 | ob] := by
      simp only [probEvent_eq_tsum_ite oa, ← ENNReal.tsum_mul_right, ite_mul, zero_mul]

end seq_map

end OracleComp
