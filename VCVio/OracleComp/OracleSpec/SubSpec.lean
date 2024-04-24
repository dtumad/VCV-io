/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Constructions

/-!
# Coercions Between Computations With Additional Oracles

This file defines a `isSubSpec` relation for pairs of `oracleSpec` where one can be
thought of as an extension of the other with additional oracles.
The definition consists of a function from query inputs in the original oracle to a
computation using the new set of oracles, such that the result of the mapping
doesn't affect the underlying probability distribution on the oracle call.

We use the notation `spec ⊂ₒ spec'` to represent that one set of oracles is a subset of another,
where the non-inclusive subset symbol reflects that we avoid defining this instance reflexively.

We define the map to output a computation rather than a new set of oracle inputs in the new spec
to avoid type checking issues, as the `query` output type will not be definitionally equal
to the `query` output type in the original `oracle_spec`, causing issues in defining `has_coe`.
In practice the mapping will still usually output a `query` call,
and the equality between the underlying distributions is generally sufficient.

From this definition we construct a `Coe` instance to coerce a computation with one set of
oracles to one with a larger set of oracles, using the sub-spec inclusion functions
We show that this coercion has no effect on `support`, `eval_dist`, or `prob_event`.
-/

open OracleSpec OracleComp BigOperators ENNReal

namespace OracleSpec

/-- Relation defining an inclusion of one set of oracles into another, where the mapping
doesn't affect the underlying probability distribution of the computation.
Informally, `spec ⊂ₒ super_spec` means that for any query to an oracle of `sub_spec`,
it can be perfectly simulated by a computation using the oracles of `super_spec`. -/
class SubSpec (spec : outParam OracleSpec) (super_spec : OracleSpec) : Type 1 where
  toFun : (i : spec.ι) → spec.domain i → OracleComp super_spec (spec.range i)
  evalDist_toFun' (i : spec.ι) (t : spec.domain i) : evalDist (toFun i t) = evalDist (query i t)

infix : 50 " ⊂ₒ " => SubSpec

namespace SubSpec

variable {spec super_spec : OracleSpec} [h : spec ⊂ₒ super_spec]

@[simp]
lemma evalDist_toFun (i : spec.ι) (t : spec.domain i) :
    evalDist (h.toFun i t) = PMF.uniformOfFintype (spec.range i) := by
  rw [h.evalDist_toFun' i t, evalDist_query]

@[simp]
lemma support_toFun (i : spec.ι) (t : spec.domain i) :
    support (h.toFun i t) = Set.univ := by
  rw [← support_evalDist, h.evalDist_toFun, PMF.support_uniformOfFintype, Set.top_eq_univ]

@[simp]
lemma finSupport_toFun (i : spec.ι) (t : spec.domain i) :
    finSupport (h.toFun i t) = Finset.univ := by
  rw [finSupport_eq_iff_support_eq_coe, support_toFun, Finset.coe_univ]

@[simp]
lemma probOutput_toFun (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
    [= u | h.toFun i t] = (↑(Fintype.card (spec.range i)) : ℝ≥0∞)⁻¹ :=
  by rw [probOutput_def, evalDist_toFun, PMF.uniformOfFintype_apply]

@[simp]
lemma probEvent_toFun (i : spec.ι) (t : spec.domain i)
    (p : spec.range i → Prop) [DecidablePred p] :
    [p | h.toFun i t] = (Finset.univ.filter p).card / Fintype.card (spec.range i) := by
  rw [probEvent_def, h.evalDist_toFun, ← evalDist_query i t, ← probEvent_def,
    probEvent_query_eq_div]

end SubSpec

/-- `coinSpec` seen as a subset of `unifSpec`, choosing a random `Bool` uniformly. -/
instance : coinSpec ⊂ₒ unifSpec where
  toFun := λ () () ↦ $ᵗ Bool
  evalDist_toFun' := λ i t ↦ by simp [evalDist_query i t]

end OracleSpec

namespace OracleComp

/-- Coerce a computation using the replacement function defined in a `SubSpec` instance. -/
instance (spec super_spec : OracleSpec) [h : spec ⊂ₒ super_spec] (α : Type)  :
    Coe (OracleComp spec α) (OracleComp super_spec α) where
      coe := λ oa ↦ simulate' (λ i t () ↦ (·, ()) <$> h.toFun i t) () oa

variable {spec super_spec : OracleSpec} [h : spec ⊂ₒ super_spec]

lemma coe_subSpec_pure (x : α) :
    (↑(pure x : OracleComp spec α) : OracleComp super_spec α) = pure x := rfl

@[simp]
lemma coe_subSpec_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (↑(oa >>= ob) : OracleComp super_spec β) = ↑oa >>= λ x ↦ ↑(ob x) := by
  simp [simulate'_def, map_eq_bind_pure_comp]

@[simp]
lemma coe_subSpec_query (i : spec.ι) (t : spec.domain i) :
    (↑(query i t) : OracleComp super_spec (spec.range i)) = h.toFun i t := by
  simp [Functor.map_map, Function.comp]

@[simp]
lemma coe_subSpec_map (oa : OracleComp spec α) (f : α → β) :
    (↑(f <$> oa) : OracleComp super_spec β) = f <$> ↑oa := by
  simp only [simulate'_map]

@[simp]
lemma coe_subSpec_seq (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
    (↑(og <*> oa) : OracleComp super_spec β) = (↑og : OracleComp super_spec (α → β)) <*> ↑oa := by
  simp [seq_eq_bind, map_eq_bind_pure_comp, simulate'_def]

@[simp]
lemma evalDist_coe_subSpec (oa : OracleComp spec α) :
    evalDist (↑oa : OracleComp super_spec α) = evalDist oa := by
  induction oa using OracleComp.inductionOn with
  | h_pure x => simp
  | h_queryBind i t oa hoa => simp [Function.comp, hoa]

@[simp]
lemma support_coe_subSpec (oa : OracleComp spec α) :
    (↑oa : OracleComp super_spec α).support = oa.support := by
  simp [← support_evalDist]

@[simp]
lemma finSupport_coe_subSpec [DecidableEq α] (oa : OracleComp spec α) :
    (↑oa : OracleComp super_spec α).finSupport = oa.finSupport := by
  simp [finSupport_eq_iff_support_eq_coe]

@[simp]
lemma probOutput_coe_subSpec (oa : OracleComp spec α) (x : α) :
    [= x | (↑oa : OracleComp super_spec α)] = [= x | oa] := by
  simp only [probOutput_def, evalDist_coe_subSpec]

@[simp]
lemma probEvent_coe_subSpec (oa : OracleComp spec α) (p : α → Prop) :
    [p | (↑oa : OracleComp super_spec α)] = [p | oa] := by
  simp only [probEvent_def, evalDist_coe_subSpec]

end OracleComp
