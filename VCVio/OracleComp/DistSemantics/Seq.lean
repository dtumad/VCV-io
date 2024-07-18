/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist

/-!
# Lemmas About the Distribution Semantics of Seq

This file collects various lemmas about the monadic sequence operation `og <*> oa`.

One especially important case is `f <$> oa <*> ob` where `f : α → β → γ`,
that runs the two computations `oa` and `ob` to get some `x` and `y` respectively,
returning only the value `f x y`.
-/

open OracleSpec ENNReal BigOperators

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β γ : Type}


-- @[simp] protected lemma return_seq_eq_map (f : α → β) : return f <*> oa = f <$> oa := rfl

-- lemma return_seq_dist_equiv_map (f : α → β ) : return f <*> oa ≃ₚ f <$> oa := dist_equiv.rfl

-- protected lemma seq_return (a : α) : og <*> return a = (λ g : α → β, g a) <$> og := seq_pure og a

-- lemma seq_return_dist_equiv (a : α) : og <*> return a ≃ₚ (λ g : α → β, g a) <$> og :=
-- dist_equiv_of_eq (seq_pure og a)

-- protected lemma seq_eq_bind_map : (og <*> oa) = (og >>= λ g, g <$> oa) := rfl

-- lemma seq_dist_equiv_bind_map : (og <*> oa) ≃ₚ (og >>= λ g, g <$> oa) := dist_equiv.rfl

-- @[simp] lemma support_seq : (og <*> oa).support = ⋃ g ∈ og.support, g '' oa.support :=
-- by simp only [oracle_comp.seq_eq_bind_map, support_bind, support_map]

-- @[simp] lemma fin_support_seq [decidable_eq α] [decidable_eq (α → β)] [decidable_eq β] :
--   (og <*> oa).fin_support = og.fin_support.bUnion (λ g, oa.fin_support.image g) :=
-- by simp [fin_support_eq_iff_support_eq_coe, mem_fin_support_iff_mem_support]

-- lemma eval_dist_seq' : ⁅og <*> oa⁆ = ⁅og⁆.bind (λ g, ⁅oa⁆.map g) :=
-- by simp [oracle_comp.seq_eq_bind_map]

-- @[simp] lemma eval_dist_seq : ⁅og <*> oa⁆ = ⁅og⁆.seq ⁅oa⁆ := eval_dist_seq' og oa

-- lemma prob_output_seq_eq_tsum_indicator (y : β) :
--   ⁅= y | og <*> oa⁆ = ∑' (g : α → β) x, ⁅= g | og⁆ * (g ⁻¹' {y}).indicator ⁅oa⁆ x :=
-- by simp only [oracle_comp.seq_eq_bind_map, prob_output_bind_eq_tsum, ← ennreal.tsum_mul_left,
--   prob_output_map_eq_tsum_indicator]

-- lemma prob_output_seq_eq_tsum_ite [decidable_eq β] (y : β) :
--   ⁅= y | og <*> oa⁆ = ∑' (g : α → β) x, if y = g x then ⁅= g | og⁆ * ⁅= x | oa⁆ else 0 :=
-- by simp only [oracle_comp.seq_eq_bind_map, prob_output_bind_eq_tsum,
--     prob_output_map_eq_tsum_ite, ← ennreal.tsum_mul_left, mul_ite, mul_zero]

-- lemma prob_output_seq_eq_sum_ite [decidable_eq α] [decidable_eq (α → β)] [decidable_eq β]
--   (y : β) : ⁅= y | og <*> oa⁆ = ∑ g in og.fin_support,
--     ∑ x in oa.fin_support, if y = g x then ⁅= g | og⁆ * ⁅= x | oa⁆ else 0 :=
-- by simp only [oracle_comp.seq_eq_bind_map, prob_output_bind_eq_sum,
--   prob_output_map_eq_sum_ite, finset.mul_sum, mul_ite, mul_zero]

-- lemma prob_event_seq_eq_tsum (p : β → Prop) :
--   ⁅p | og <*> oa⁆ = ∑' g, ⁅= g | og⁆ * ⁅p ∘ g | oa⁆ :=
-- by simp [oracle_comp.seq_eq_bind_map, prob_event_bind_eq_tsum]

-- lemma prob_event_seq_eq_tsum_ite (p : β → Prop) [decidable_pred p] :
--   ⁅p | og <*> oa⁆ = ∑' (g : α → β) x, if p (g x) then ⁅= g | og⁆ * ⁅= x | oa⁆ else 0 :=
-- by simp_rw [prob_event_seq_eq_tsum, prob_event_eq_tsum_ite, ← ennreal.tsum_mul_left,
--   mul_ite, mul_zero]

-- end seq

-- section seq_assoc

-- protected lemma oracle_comp.seq_assoc (oa : oracle_comp spec α) (ob : oracle_comp spec (α → β))
--   (oc : oracle_comp spec (β → γ)) : oc <*> (ob <*> oa) = (∘) <$> oc <*> ob <*> oa :=
-- by simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]

-- end seq_assoc

-- section seq_map

-- lemma seq_dist_equiv_seq {oa oa' : oracle_comp spec α} {og og' : oracle_comp spec (α → β)}
--   (h1 : oa ≃ₚ oa')
--   (h : ∀ x ∈ oa.support, ((λ f : α → β, f x) <$> og) ≃ₚ ((λ f : α → β, f x) <$> og')) :
--   og <*> oa ≃ₚ og' <*> oa' :=
-- begin
--   simp only [seq_eq_bind_map, map_eq_bind_pure_comp],
--   rw_dist_equiv [bind_bind_dist_equiv_comm og, bind_bind_dist_equiv_comm og', h1.symm],
--   pairwise_dist_equiv 1 with x hx,
--   exact h x hx
-- end

-- lemma seq_map_dist_equiv_seq_map {oa oa' : oracle_comp spec α} {ob ob' : oracle_comp spec β}
--   (f g : α → β → γ) (h : oa ≃ₚ oa') (h' : ob ≃ₚ ob')
--   (hfg : ∀ x ∈ oa.support, ∀ y ∈ ob.support, f x y = g x y) :
--   f <$> oa <*> ob ≃ₚ g <$> oa' <*> ob' :=
-- begin
--   refine seq_dist_equiv_seq h' (λ y hy, _),
--   simp only [map_map_eq_map_comp, function.comp],
--   refine map_dist_equiv_map (λ x hx, hfg x hx y hy) h,
-- end

-- lemma seq_map_dist_equiv_map_left {oa : oracle_comp spec α} {ob : oracle_comp spec β}
--   (f : α → β → γ) (g : α → γ) (h : ∀ x ∈ oa.support, ∀ y ∈ ob.support, f x y = g x) :
--   f <$> oa <*> ob ≃ₚ g <$> oa :=
-- begin
--   rw_dist_equiv [seq_map_dist_equiv_seq_map f (λ x y, g x) dist_equiv.rfl dist_equiv.rfl h],
--   simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc],
--   rw_dist_equiv [bind_const_dist_equiv],
-- end

-- lemma seq_map_dist_equiv_map_right {oa : oracle_comp spec α} {ob : oracle_comp spec β}
--   (f : α → β → γ) (g : β → γ) (h : ∀ x ∈ oa.support, ∀ y ∈ ob.support, f x y = g y) :
--   f <$> oa <*> ob ≃ₚ g <$> ob :=
-- begin
--   rw_dist_equiv [seq_map_dist_equiv_seq_map f (λ x y, g y) dist_equiv.rfl dist_equiv.rfl h],
--   simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]
-- end

-- variables (oa oa' : oracle_comp spec α) (ob ob' : oracle_comp spec β) (f : α → β → γ)

-- lemma seq_map_eq_bind_bind : f <$> oa <*> ob = do {x ← oa, y ← ob, return (f x y)} :=
-- by simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, pure_bind]

-- @[simp] lemma support_seq_map : (f <$> oa <*> ob).support = set.image2 f oa.support ob.support :=
-- by simp_rw [support_seq, support_map, set.mem_image, set.Union_exists, set.bUnion_and',
--   set.Union_Union_eq_right, set.image2, set.ext_iff, exists_and_distrib_left, set.mem_Union,
--   set.mem_image, exists_prop, set.mem_set_of_eq, iff_self, implies_true_iff]

-- @[simp] lemma fin_support_seq_map [decidable_eq α] [decidable_eq β] [decidable_eq γ] :
--   (f <$> oa <*> ob).fin_support = finset.image₂ f oa.fin_support ob.fin_support :=
-- by simp_rw [fin_support_eq_iff_support_eq_coe, finset.coe_image₂, coe_fin_support, support_seq_map]

-- lemma eval_dist_seq_map : ⁅f <$> oa <*> ob⁆ = (⁅oa⁆.map f).seq ⁅ob⁆ :=
-- by rw [eval_dist_seq, eval_dist_map]

lemma probOutput_seq_map_eq_tsum (oa : OracleComp spec α) (ob : OracleComp spec β)
    (f : α → β → γ) (z : γ) : [= z | f <$> oa <*> ob] =
      ∑' x, ∑' y, [= x | oa] * [= y | ob] * [= z | (pure (f x y) : OracleComp spec γ)] := by
  simp only [map_eq_bind_pure_comp, Function.comp, seq_eq_bind, bind_assoc, pure_bind,
    probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left, mul_assoc]





-- /-- TODO: maybe defaulting to something like this is better than using indicator? -/
-- @[simp] lemma prob_output_seq_map_eq_tsum' (z : γ) :
--   ⁅= z | f <$> oa <*> ob⁆ = ∑' x y, ⁅= x | oa⁆ * ⁅= y | ob⁆ * ⁅= z | return' !spec! (f x y)⁆ :=
-- by simp_rw [seq_map_eq_bind_bind, prob_output_bind_eq_tsum, ← ennreal.tsum_mul_left, mul_assoc]

-- @[simp] lemma prob_output_seq_map_eq_tsum [decidable_eq γ] (z : γ) :
--   ⁅= z | f <$> oa <*> ob⁆ = ∑' x y, if z = f x y then ⁅= x | oa⁆ * ⁅= y | ob⁆ else 0 :=
-- by simp_rw [prob_output_seq_map_eq_tsum', prob_output_return, mul_boole]

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

-- section uncurry

-- lemma prob_event_seq_map_eq_prob_event_comp_uncurry (f : α → β → γ) (p : γ → Prop) :
--   ⁅p | f <$> oa <*> ob⁆ = ⁅p ∘ function.uncurry f | prod.mk <$> oa <*> ob⁆ :=
-- by simpa only [← prob_event_map _ (function.uncurry f), map_seq, map_map_eq_map_comp]

-- end uncurry

-- section injective2

-- variable {f}

-- lemma mem_support_seq_map_iff_of_injective2 (hf : function.injective2 f) (x : α) (y : β) :
--   f x y ∈ (f <$> oa <*> ob).support ↔ x ∈ oa.support ∧ y ∈ ob.support :=
-- by rw [support_seq_map, set.mem_image2_iff hf]

-- lemma mem_fin_support_seq_map_iff_of_injective2 [decidable_eq α] [decidable_eq β]
--   [decidable_eq γ] (hf : function.injective2 f) (x : α) (y : β) :
--   f x y ∈ (f <$> oa <*> ob).fin_support ↔ x ∈ oa.fin_support ∧ y ∈ ob.fin_support :=
-- by simp_rw [mem_fin_support_iff_mem_support, mem_support_seq_map_iff_of_injective2 oa ob hf]

lemma probOutput_seq_map_eq_mul_of_injective2 {α β γ : Type}
    (oa : OracleComp spec α) (ob : OracleComp spec β)
    (f : α → β → γ) (hf : Function.Injective2 f) (x : α) (y : β) :
    [= f x y | f <$> oa <*> ob] = [= x | oa] * [= y | ob] := by
  rw [probOutput_seq_map_eq_tsum]
  rw [← ENNReal.tsum_prod]
  refine (tsum_eq_single (x, y) (λ (x', y') h ↦ ?_)).trans ?_
  · suffices f x y ≠ f x' y' by simp [this]
    exact λ h' ↦ h (Prod.eq_iff_fst_eq_snd_eq.2 (hf h'.symm))
  · rw [probOutput_pure_self, mul_one]







-- lemma prob_output_seq_map_eq_mul_of_injective2 (hf : function.injective2 f) (x : α) (y : β) :
--   ⁅= f x y | f <$> oa <*> ob⁆ = ⁅= x | oa⁆ * ⁅= y | ob⁆ :=
-- begin
--   haveI : decidable_eq γ := classical.dec_eq γ,
--   rw [prob_output_seq_map_eq_tsum, ← ennreal.tsum_prod],
--   refine trans (tsum_eq_single (x, y) (λ z hz, if_neg (λ h, hz (prod.eq_iff_fst_eq_snd_eq.2
--     (hf.eq_iff.1 h.symm))))) (if_pos rfl),
-- end

-- end injective2

-- section indep_eq_mul

-- /-- If the results of the computations `oa` and `ob` are combined with some function `f`,
-- and there exists unique `x` and `y` such that `f x y = z` (given as explicit arguments),
-- then the probability of getting `z` as an output of `f <$> oa <*> ob`
-- is the product of probabilities of getting `x` and `y` from `oa` and `ob` respectively. -/
-- lemma prob_output_seq_map_eq_mul {f : α → β → γ} {z : γ} (x : α) (y : β)
--   (h : ∀ x' ∈ oa.support, ∀ y' ∈ ob.support, z = f x' y' ↔ x' = x ∧ y' = y):
--   ⁅= z | f <$> oa <*> ob⁆ = ⁅= x | oa⁆ * ⁅= y | ob⁆ :=
-- begin
--   simp_rw [imp_forall_iff, ← and_imp, ← prod.forall'] at h,
--   haveI : decidable_eq γ := classical.dec_eq γ,
--   rw [prob_output_seq_map_eq_tsum, ← ennreal.tsum_prod],
--   refine trans (tsum_eq_single (x, y) (λ z' hz, _)) _,
--   { simp_rw [ite_eq_right_iff, mul_eq_zero, prob_output_eq_zero_iff, ← not_and_distrib],
--     refine imp_not_comm.1 (λ hz' hzf, hz _),
--     rw [← ((h z' hz').1 hzf).1, ← ((h z' hz').1 hzf).2, prod.mk.eta] },
--   { simp only [ite_eq_left_iff, zero_eq_mul, prob_output_eq_zero_iff, ← not_and_distrib],
--     refine mt (λ hxy, (h (x, y) hxy).2 ⟨rfl, rfl⟩) }
-- end

-- /-- If the results of the computations `oa` and `ob` are combined with some function `f`,
-- and `e` is an event such that outputs of `f` are in `e` iff the individual components
-- lie in some other events `e1` and `e2`, then the probability of the event `e` is the
-- product of the probabilites holding individually.
-- For example this applies if `f` is `::`, `e` is defined elementwise,
-- and `e1` and `e2` are the portions of `e` for the head and tail respectively. -/
-- lemma prob_event_seq_map_eq_mul (oa : oracle_comp spec α) (ob : oracle_comp spec β)
--   (f : α → β → γ) (p : γ → Prop) (q1 : α → Prop) (q2 : β → Prop)
--   (h : ∀ x ∈ oa.support, ∀ y ∈ ob.support, p (f x y) ↔ q1 x ∧ q2 y) :
--   ⁅p | f <$> oa <*> ob⁆ = ⁅q1 | oa⁆ * ⁅q2 | ob⁆ :=
-- begin
--   haveI : decidable_pred p := classical.dec_pred p,
--   haveI : decidable_pred q1 := classical.dec_pred q1,
--   haveI : decidable_pred q2 := classical.dec_pred q2,
--   simp_rw [prob_event_seq_map_eq_tsum, ← ennreal.tsum_prod, prob_event_eq_tsum_ite,
--     ← ennreal.tsum_mul_right, ← ennreal.tsum_mul_left, ← ennreal.tsum_prod, ite_mul,
--     zero_mul, mul_ite, mul_zero, ← ite_and],
--   refine tsum_congr (λ z, _),
--   by_cases hz : z.1 ∈ oa.support ∧ z.2 ∈ ob.support,
--   { simp only [h z.1 hz.1 z.2 hz.2] },
--   { cases (not_and_distrib.1 hz) with hz hz;
--     simp only [prob_output_eq_zero, hz, not_false_iff, zero_mul, mul_zero, if_t_t] }
-- end

-- end indep_eq_mul

-- end seq_map

-- section comm

-- variables (oa oa' : oracle_comp spec α) (ob ob' : oracle_comp spec β)

-- @[pairwise_dist_equiv] lemma seq_map_dist_equiv_comm_swap (f : α → β → γ) :
--   f <$> oa <*> ob ≃ₚ f.swap <$> ob <*> oa :=
-- by simp only [seq_map_eq_bind_bind, bind_bind_dist_equiv_comm]

-- lemma seq_map_dist_equiv_comm (f : α → α → β) (hf : ∀ x x', f x x' = f x' x) :
--   f <$> oa <*> oa' ≃ₚ f <$> oa' <*> oa :=
-- have f.swap = f := by simp only [function.funext_iff, function.swap, hf, eq_self_iff_true],
-- (seq_map_dist_equiv_comm_swap oa oa' f).trans (by rw [this])

-- lemma seq_seq_dist_equiv_comm (f : α → β → β)
--   (hf : ∀ x ∈ oa.support, ∀ x' ∈ oa'.support, f x ∘ f x' = f x' ∘ f x) :
--   (f <$> oa') <*> (f <$> oa <*> ob) ≃ₚ (f <$> oa) <*> (f <$> oa' <*> ob) :=
-- begin
--   simp only [seq_eq_bind_map, map_bind, map_map_eq_map_comp],
--   rw_dist_equiv [bind_bind_dist_equiv_comm],
--   refine bind_dist_equiv_bind_of_dist_equiv_right _ (λ g hg, _),
--   refine bind_dist_equiv_bind_of_dist_equiv_right _ (λ g' hg', _),
--   rw [mem_support_map_iff] at hg hg',
--   obtain ⟨x, hx, rfl⟩ := hg,
--   obtain ⟨y, hy, rfl⟩ := hg',
--   rw [hf x hx y hy],
-- end

-- end comm

-- end oracle_comp


end OracleComp
