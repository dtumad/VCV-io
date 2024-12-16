/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleComp
import Mathlib.Data.Set.Finite.Lattice

/-!
# Support of a Computation

This file defines a function `OracleComp.support : OracleComp spec α → Set α` that
gives the set of possible outputs of a computation, assuming all oracle outputs are possible.

If the final output type has decidable equality we can also define a function
`OracleComp.finSupport : OracleComp spec α → Finset α` with the same property.
This relies on decidable equality instances in `OracleSpec` as well, and the definition
would need to be adjusted if those were moved into a seperate typeclass.

We avoid using `(evalDist oa).support` as the definition of the support, as this forces
noncomputability due to the use of real numbers, and also makes defining `finSupport` harder.
-/

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- The `support` of a computation `oa` is the set of all possible output values,
assuming that all output values of the oracles are possible.
This is naturally compatible with `evalDist` where the oracles respond uniformly. -/
def support : (oa : OracleComp spec α) → Set α
  | pure' _ x => {x}
  | queryBind' _ _ _ oa => ⋃ u, (oa u).support
  | failure' _ => ∅

-- lemma support_pure' (x : α) : support (pure' α x : OracleComp spec α) = {x} := rfl

-- lemma support_queryBind' (i : ι) (t : spec.domain i)
--     (oa : spec.range i → OracleComp spec α) :
--     support (queryBind' i t α oa) = ⋃ u, (oa u).support := rfl

/-- Given a `DecidableEq` instance on the return type, we can construct
a `Finset` of possible outputs. Without this we can't remove duplicate values from
the list of outputs being constructed. This also relies on the `DecidableEq` instances
on `spec.range i` that are included in the definition of `OracleSpec`. -/
def finSupport [DecidableEq α] : (oa : OracleComp spec α) → Finset α
  | pure' _ x => {x}
  | queryBind' _ _ _ oa => Finset.biUnion Finset.univ (λ u ↦ (oa u).finSupport)
  | failure' _ => ∅

-- lemma finSupport_pure' [DecidableEq α] (x : α) :
--     finSupport (pure' α x : OracleComp spec α) = {x} := rfl

-- lemma finSupport_queryBind' [DecidableEq α] (i : ι) (t : spec.domain i)
--     (oa : spec.range i → OracleComp spec α) :
--   finSupport (queryBind' i t α oa) =
--     Finset.biUnion Finset.univ (λ u ↦ (oa u).finSupport) := rfl

section basic

@[simp] lemma support_pure (x : α) :
  (pure x : OracleComp spec α).support = {x} := rfl
@[simp] lemma finSupport_pure (x : α) [DecidableEq α] :
  (pure x : OracleComp spec α).finSupport = {x} := rfl

@[simp] lemma support_failure :
  (failure : OracleComp spec α).support = ∅ := rfl
@[simp] lemma finSupport_failure [DecidableEq α] :
  (failure : OracleComp spec α).finSupport = ∅ := rfl

@[simp] lemma support_query (i : ι) (t : spec.domain i) :
    (query i t).support = Set.univ := by
  simpa only [query_def, support] using Set.iUnion_of_singleton (spec.range i)
@[simp] lemma finSupport_query (i : ι) (t : spec.domain i) :
    (query i t).finSupport = Finset.univ := by
  simpa only [query_def, finSupport] using Finset.biUnion_singleton_eq_self

@[simp]
lemma support_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).support = ⋃ x ∈ oa.support, (ob x).support := by
  induction oa using OracleComp.inductionOn with
  | pure _ => simp
  | query_bind i t oa hoa =>
      simpa [bind_assoc, ← queryBind'_eq_queryBind, support, hoa] using Set.iUnion_comm _
  | failure => simp

@[simp]
lemma finSupport_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    [hα : DecidableEq α] [hβ : DecidableEq β] : (oa >>= ob).finSupport =
      oa.finSupport.biUnion (λ x ↦ (ob x).finSupport) := by
  induction oa using OracleComp.inductionOn generalizing hα hβ with
  | pure _ => simp
  | query_bind i t oa hoa =>
      apply Finset.coe_inj.1
      simpa [bind_assoc, ← queryBind'_eq_queryBind, finSupport, hoa] using Set.iUnion_comm _
  | failure => simp

lemma mem_support_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    y ∈ (oa >>= ob).support ↔ ∃ x ∈ oa.support, y ∈ (ob x).support := by simp
lemma mem_finSupport_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    [hoa : DecidableEq α] [hob : DecidableEq β] (y : β) : y ∈ (oa >>= ob).finSupport ↔
      ∃ x ∈ oa.finSupport, y ∈ (ob x).finSupport := by simp

/-- The support of a computation is finite when viewed as a type. -/
instance support_finite (oa : OracleComp spec α) : Finite ↥(oa.support) := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact Set.finite_singleton x
  | query_bind _ _ oa hoa => exact Set.finite_iUnion hoa
  | failure => exact Set.toFinite ∅

/-- With a `DecidableEq` instance we can show that the support is actually a `Fintype`,
rather than just `Finite` as in `support_finite`. -/
instance support_fintype [DecidableEq α] (oa : OracleComp spec α) :
    Fintype ↥oa.support := by
  induction oa using OracleComp.induction with
  | pure x => exact Fintype.subtypeEq x
  | query_bind i t oa hoa => simpa using Set.fintypeiUnion _
  | failure => exact Set.fintypeEmpty

end basic

section coe

/-- `finSupport` when viewed as a `Set` gives the regular `support` of the computation.  -/
@[simp]
lemma coe_finSupport [DecidableEq α] (oa : OracleComp spec α) : ↑oa.finSupport = oa.support := by
  induction oa using OracleComp.induction with
  | pure x => apply Finset.coe_singleton
  | query_bind i t oa hoa => simp [hoa]
  | failure => apply Finset.coe_empty

variable [DecidableEq α] (oa : OracleComp spec α) (s : Finset α)

lemma finSupport_eq_iff_support_eq_coe : oa.finSupport = s ↔ oa.support = ↑s :=
  Finset.coe_inj.symm.trans (by rw [coe_finSupport])
lemma eq_finSupport_iff_coe_eq_support : s = oa.finSupport ↔ ↑s = oa.support :=
  Finset.coe_inj.symm.trans (by rw [coe_finSupport])

lemma finSupport_subset_iff_support_subset_coe : oa.finSupport ⊆ s ↔ oa.support ⊆ ↑s :=
  Finset.coe_subset.symm.trans (by rw [coe_finSupport])
lemma subset_finSupport_iff_coe_subset_support : s ⊆ oa.finSupport ↔ ↑s ⊆ oa.support :=
  Finset.coe_subset.symm.trans (by rw [coe_finSupport])

lemma mem_finSupport_iff_mem_support (x : α) : x ∈ oa.finSupport ↔ x ∈ oa.support := by
  rw [← Finset.mem_coe, coe_finSupport]

lemma mem_finSupport_of_mem_support {x : α} (hx : x ∈ oa.support) : x ∈ oa.finSupport :=
  (mem_finSupport_iff_mem_support oa x).2 hx
lemma mem_support_of_mem_finSupport {x : α} (hx : x ∈ oa.finSupport) : x ∈ oa.support :=
  (mem_finSupport_iff_mem_support oa x).1 hx

end coe

section decidable

/-- If the output type of a computation has `DecidableEq` then membership in the `support`
of a computation is also decidable as a predicate.
NOTE: will need to be restricted if we allow infinite oracle codomains. -/
instance decidablePred_mem_support [hα : DecidableEq α] (oa : OracleComp spec α) :
    DecidablePred (· ∈ oa.support) := by
  induction oa using OracleComp.induction with
  | pure x => exact λ y ↦ hα y x
  | failure => exact λ _ ↦ Decidable.isFalse (not_false)
  | query_bind i t oa hoa =>
      simp only [support_bind, support_query, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      exact λ _ ↦ Fintype.decidableExistsFintype

/-- Membership in `finSupport` is a decidable predicate if it's defined. -/
instance decidablePred_mem_finSupport [DecidableEq α] (oa : OracleComp spec α) :
    DecidablePred (· ∈ oa.finSupport) := by
  simp [mem_finSupport_iff_mem_support]
  apply decidablePred_mem_support

end decidable

section nonempty

variable (oa : OracleComp spec α)

-- lemma defaultResult_mem_support : oa.defaultResult ∈ oa.support := by
--   induction oa using OracleComp.inductionOn with
--   | h_pure x => simp only [defaultResult, support_pure, Set.mem_singleton_iff]
--   | h_queryBind i t oa hoa =>
--       have : ∃ u, defaultResult (oa default) ∈ (oa u).support := ⟨default, hoa default⟩
--       simpa only [defaultResult, OracleComp.bind'_eq_bind, pure_bind,support_bind,support_query,
--         Set.mem_univ, Set.iUnion_true, Set.mem_iUnion] using this

-- lemma exists_mem_support : ∃ x : α, x ∈ oa.support :=
--   ⟨defaultResult oa, defaultResult_mem_support oa⟩

-- lemma defaultResult_mem_finSupport [DecidableEq α] : oa.defaultResult ∈ oa.finSupport := by
--   simpa only [mem_finSupport_iff_mem_support] using defaultResult_mem_support oa

-- @[simp] lemma support_nonempty : oa.support.Nonempty :=
--   ⟨defaultResult oa, defaultResult_mem_support oa⟩

-- @[simp] lemma finSupport_nonempty [DecidableEq α] : oa.finSupport.Nonempty :=
--   ⟨defaultResult oa, defaultResult_mem_finSupport oa⟩

-- @[simp] lemma support_ne_empty : oa.support ≠ ∅ := (support_nonempty oa).ne_empty
-- @[simp] lemma finSupport_ne_empty [DecidableEq α] : oa.finSupport ≠ ∅ :=
--   Finset.ne_empty_of_mem (defaultResult_mem_finSupport oa)

-- @[simp] lemma support_eq_singleton_iff (x : α) :
--     oa.support = {x} ↔ oa.support ⊆ {x} := by
--   rw [oa.support_nonempty.subset_singleton_iff]
-- @[simp] lemma finSupport_eq_singleton_iff [DecidableEq α] (x : α) :
--     oa.finSupport = {x} ↔ oa.finSupport ⊆ {x} := by
--   simp [finSupport_eq_iff_support_eq_coe]

end nonempty

@[simp] lemma support_eqRec (oa : OracleComp spec α) (h : α = β) :
    (h ▸ oa).support = h.symm ▸ oa.support := by
  induction h; rfl
@[simp] lemma finSupport_eqRec [hα : DecidableEq α] [hβ : DecidableEq β]
    (oa : OracleComp spec α) (h : α = β) :
    @finSupport _ _ _ hβ (h ▸ oa : OracleComp spec β) = h.symm ▸ @finSupport _ _ _ hα oa := by
  refine Finset.ext (λ x ↦ ?_)
  simp [mem_finSupport_iff_mem_support]
  induction h -- We can't do this earlier without running into trouble with `DecidableEq`
  exact Iff.symm (mem_finSupport_iff_mem_support oa x)

@[simp] lemma support_map (oa : OracleComp spec α) (f : α → β) :
    (f <$> oa).support = f '' oa.support := by
  simp only [map_eq_pure_bind, ← Set.image_eq_iUnion, support_bind, support_pure]
@[simp] lemma fin_support_map [DecidableEq α] [DecidableEq β]
    (oa : OracleComp spec α) (f : α → β) : (f <$> oa).finSupport = oa.finSupport.image f := by
  simp [finSupport_eq_iff_support_eq_coe]

@[simp] lemma support_ite (p : Prop) [Decidable p] (oa oa' : OracleComp spec α) :
    (ite p oa oa').support = ite p oa.support oa'.support :=
  apply_ite support p oa oa'
@[simp] lemma finSupport_ite [DecidableEq α] (p : Prop) [Decidable p]
    (oa oa' : OracleComp spec α) : (ite p oa oa').finSupport =
      ite p oa.finSupport oa'.finSupport :=
  apply_ite finSupport p oa oa'

@[simp] lemma support_coin : coin.support = {true, false} :=
  by simp [Set.ext_iff, coin, support_query (spec := coinSpec)]
@[simp] lemma finSupport_coin : coin.finSupport = {true, false} :=
  by simp [finSupport_eq_iff_support_eq_coe]

@[simp] lemma support_uniformFin (n : ℕ) : ($[0..n]).support = Set.univ := support_query n _
@[simp] lemma finSupport_uniformFin (n : ℕ) : ($[0..n]).finSupport = Finset.univ :=
  finSupport_query n _

example : support (do
    let b ← coin; let b' ← coin
    let x ← (if b && b' then return 0 else return 1);
    let z ← (if b && b' then return x else return 0);
    return (x * z)) = {0} :=
  by simp [Set.eq_singleton_iff_unique_mem]

example : finSupport (do
    let b ← coin; let b' ← coin
    let x ← (if b || b' then return 0 else return 1);
    let z ← (if b || b' then return x else return 0);
    return (x * z)) = {0} :=
  by simp

end OracleComp
