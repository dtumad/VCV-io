/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate
import VCVio.OracleComp.Constructions.UniformSelect

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

variable {ι₁ ι₂ : Type} {spec : OracleSpec ι₁} {superSpec : OracleSpec ι₂} {α β γ : Type}

namespace OracleSpec

/-- Relation defining an inclusion of one set of oracles into another, where the mapping
doesn't affect the underlying probability distribution of the computation.
Informally, `spec ⊂ₒ superSpec` means that for any query to an oracle of `sub_spec`,
it can be perfectly simulated by a computation using the oracles of `superSpec`.

We avoid implementing this via the built-in subset type as we care about the actual data
of the mapping rather than just its existence, which is needed when defining type coercions. -/
class SubSpec (spec : OracleSpec ι₁) (superSpec : OracleSpec ι₂) : Type 1 where
  toFun (i : ι₁) (t : spec.domain i) : OracleComp superSpec (spec.range i)
  evalDist_toFun' (i : ι₁) (t : spec.domain i) : evalDist (toFun i t) = evalDist (query i t)

-- Note: this version has some nicer properties but is usually more annoying.
-- class SubSpec' (spec : OracleSpec ι₁) (superSpec : OracleSpec ι₂) : Type 1 where
--   index_map (i : ι₁) : ι₂
--   input_map (i : ι₁) (t : spec.domain i) : superSpec.domain (index_map i)
--   range_eq (i : ι₁) : superSpec.range (index_map i) = spec.range i

-- def liftComp' [h : SubSpec' spec superSpec] (oa : OracleComp spec α) : OracleComp superSpec α :=
--   simulate' (λ i t () ↦ h.range_eq i ▸ (·, ()) <$>
--      query (h.index_map i) (h.input_map i t)) () oa

infix : 50 " ⊂ₒ " => SubSpec

namespace SubSpec

variable [h : spec ⊂ₒ superSpec]

@[simp]
lemma evalDist_toFun (i : ι₁) (t : spec.domain i) :
    evalDist (h.toFun i t) = PMF.uniformOfFintype (spec.range i) := by
  sorry
  -- rw [h.evalDist_toFun' i t, evalDist_query]

@[simp]
lemma support_toFun (i : ι₁) (t : spec.domain i) :
    support (h.toFun i t) = Set.univ := by
  sorry
  -- rw [← support_evalDist, h.evalDist_toFun, PMF.support_uniformOfFintype, Set.top_eq_univ]

@[simp]
lemma finSupport_toFun (i : ι₁) (t : spec.domain i) :
    finSupport (h.toFun i t) = Finset.univ := by
  rw [finSupport_eq_iff_support_eq_coe, support_toFun, Finset.coe_univ]

@[simp]
lemma probOutput_toFun (i : ι₁) (t : spec.domain i) (u : spec.range i) :
    [= u | h.toFun i t] = (↑(Fintype.card (spec.range i)) : ℝ≥0∞)⁻¹ :=
  sorry --by rw [probOutput_def, evalDist_toFun, PMF.uniformOfFintype_apply]

@[simp]
lemma probEvent_toFun (i : ι₁) (t : spec.domain i)
    (p : spec.range i → Prop) [DecidablePred p] :
    [p | h.toFun i t] = (Finset.univ.filter p).card / Fintype.card (spec.range i) := by
  sorry
  -- rw [probEvent_def, h.evalDist_toFun, ← evalDist_query i t, ← probEvent_def,
  --   probEvent_query_eq_div]

section liftComp

def liftComp [h : spec ⊂ₒ superSpec] (oa : OracleComp spec α) : OracleComp superSpec α :=
  simulate' (λ i t () ↦ (·, ()) <$> h.toFun i t) () oa

lemma liftComp_def (oa : OracleComp spec α) : h.liftComp oa =
    simulate' (λ i t () ↦ (·, ()) <$> h.toFun i t) () oa := rfl

lemma liftComp_pure (x : α) : h.liftComp (pure x : OracleComp spec α) = pure x :=
  simulate'_pure _ () x

lemma liftComp_query (i : ι₁) (t : spec.domain i) :
    h.liftComp (query i t) = h.toFun i t :=
  by rw [liftComp, simulate'_query, fst_map_prod_mk_of_subsingleton]

lemma liftComp_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    h.liftComp (oa >>= ob) = h.liftComp oa >>= λ x ↦ h.liftComp (ob x) := by
  simp only [liftComp, simulate'_bind]
  rw [simulate_eq_map_simulate'_of_subsingleton _ _ _ ()]
  simp [simulate', Functor.map_map, Function.comp, map_eq_bind_pure_comp]

@[simp]
lemma evalDist_liftComp (oa : OracleComp spec α) :
    evalDist (h.liftComp oa) = evalDist oa := by
  sorry
  -- induction oa using OracleComp.inductionOn with
  -- | pure => simp [liftComp_pure]
  -- | query_bind i t oa hoa =>
  --     simp only [liftComp_bind, liftComp_query, evalDist_bind, evalDist_toFun, evalDist_query]
  --     exact congr_arg _ (funext hoa)

@[simp]
lemma support_liftComp (oa : OracleComp spec α) :
    (h.liftComp oa).support = oa.support :=
  Set.ext (mem_support_iff_of_evalDist_eq <| evalDist_liftComp oa)

@[simp]
lemma finSupport_liftComp [DecidableEq α] (oa : OracleComp spec α) :
    (h.liftComp oa).finSupport = oa.finSupport :=
  Finset.ext (mem_finSupport_iff_of_evalDist_eq <| evalDist_liftComp oa)

@[simp]
lemma probOutput_liftComp (oa : OracleComp spec α) (x : α) :
    [= x | h.liftComp oa] = [= x | oa] := by
  simp only [probOutput_def, evalDist_liftComp]

@[simp]
lemma probEvent_liftComp (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    [p | h.liftComp oa] = [p | oa] := by
  simp only [probEvent_def, evalDist_liftComp]

end liftComp

section instances

/-- The empty set of oracles is a subspec of any other oracle set.
We require `ι` to be inhabited to prevent the reflexive case.  -/
instance {ι : Type} [Inhabited ι] {spec : OracleSpec ι} : []ₒ ⊂ₒ spec where
  toFun := λ i ↦ Empty.elim i
  evalDist_toFun' := λ i ↦ Empty.elim i

/-- A computation with no oracles can be viewed as one with any other set of oracles. -/
instance coe_subSpec_empty {ι : Type} [Inhabited ι] {spec : OracleSpec ι} {α : Type} :
    Coe (OracleComp []ₒ α) (OracleComp spec α) where
  coe := liftComp

lemma coe_subSpec_empty_eq_liftComp {ι : Type} [Inhabited ι] {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp []ₒ α) : (↑oa : OracleComp spec α) = liftComp oa := rfl

/-- `coinSpec` seen as a subset of `unifSpec`, choosing a random `Bool` uniformly. -/
instance : coinSpec ⊂ₒ unifSpec where
  toFun := λ () () ↦ $ᵗ Bool
  evalDist_toFun' := λ i t ↦ sorry --by simp [evalDist_query i t]

instance coe_subSpec_coinSpec_unifSpec {α : Type} :
    Coe (OracleComp coinSpec α) (ProbComp α) where
  coe := liftComp

lemma coe_subSpec_coinSpec_unifSpec_eq_liftComp {α : Type} (oa : OracleComp coinSpec α) :
    (↑oa : ProbComp α) = liftComp oa := rfl

end instances

end SubSpec

end OracleSpec

namespace OracleComp

/-- View a probabalistic computation as one with a larger set of oracles.
We make this a special instance as it's often needed in situations where the
type-class instance is not yet available (e.g. defining security experiments). -/
instance {ι : Type} (spec : OracleSpec ι) [unifSpec ⊂ₒ spec] (α : Type) :
    Coe (ProbComp α) (OracleComp spec α) where
  coe := λ oa ↦ SubSpec.liftComp oa

end OracleComp
