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
-- class SubSpec (spec : OracleSpec ι₁) (superSpec : OracleSpec ι₂) : Type 1 where
--   toFun (i : ι₁) (t : spec.domain i) : OracleComp superSpec (spec.range i)

class SubSpec (spec : OracleSpec ι₁) (superSpec : OracleSpec ι₂)
  extends MonadLift (OracleQuery spec) (OracleQuery superSpec) where
  -- toFun : {α : Type} → OracleQuery spec α → OracleQuery superSpec α
-- Note: this version has some nicer properties but is usually more annoying.
-- class SubSpec' (spec : OracleSpec ι₁) (superSpec : OracleSpec ι₂) : Type 1 where
--   index_map (i : ι₁) : ι₂
--   input_map (i : ι₁) (t : spec.domain i) : superSpec.domain (index_map i)
--   range_eq (i : ι₁) : superSpec.range (index_map i) = spec.range i

-- def liftComp' [h : SubSpec' spec superSpec] (oa : OracleComp spec α) : OracleComp superSpec α :=
--   simulate' (λ i t () ↦ h.range_eq i ▸ (·, ()) <$>
--      query (h.index_map i) (h.input_map i t)) () oa

infix : 50 " ⊂ₒ " => SubSpec

-- class lawfulSubSpec (spec : OracleSpec ι₁) (superSpec : OracleSpec ι₂)
--     [h : spec ⊂ₒ superSpec] [spec.FiniteRange] [superSpec.FiniteRange] where
--   evalDist_toFun' (i : ι₁) (t : spec.domain i) :
--     evalDist (h.toFun i t) = evalDist (query i t : OracleComp spec _)

namespace SubSpec

variable [h : spec ⊂ₒ superSpec]


  -- [lawfulSubSpec spec superSpec]

@[simp]
lemma evalDist_toFun [superSpec.FiniteRange] [Fintype α] [Nonempty α] (q : OracleQuery spec α) :
    evalDist (h.monadLift q : OracleComp superSpec α) =
      OptionT.lift (PMF.uniformOfFintype α) := by
  simp [PMF.monad_map_eq_map]
  refine congr_arg OptionT.lift ?_
  ext x
  sorry
  -- simp


@[simp]
lemma support_toFun (q : OracleQuery spec α) :
    support (h.monadLift q : OracleComp superSpec α) = Set.univ := by
  rw [support_liftM]

@[simp]
lemma finSupport_toFun [spec.DecidableEq] [superSpec.DecidableEq] [superSpec.FiniteRange]
    [DecidableEq α] [Fintype α] (q : OracleQuery spec α) :
    finSupport (h.monadLift q : OracleComp superSpec α) = Finset.univ := by
  rw [finSupport_liftM]

@[simp]
lemma probOutput_toFun [superSpec.FiniteRange] [Fintype α]
    (q : OracleQuery spec α) (u : α) :
    [= u | (h.monadLift q : OracleComp superSpec α)] =
      (↑(Fintype.card α) : ℝ≥0∞)⁻¹ := by
  rw [probOutput_liftM]

@[simp]
lemma probEvent_toFun [superSpec.FiniteRange] [Fintype α]
    (q : OracleQuery spec α) (p : α → Prop) [DecidablePred p] :
    [p | (h.monadLift q : OracleComp superSpec α)] =
      (Finset.univ.filter p).card / Fintype.card α := by
  rw [probEvent_liftM_eq_div]

section liftComp

def liftingOracle (spec : OracleSpec ι₁) (superSpec : OracleSpec ι₂)
    [h : spec ⊂ₒ superSpec] : spec →[Unit]ₛₒ superSpec :=
  λ i t ↦ h.monadLift (query i t)

def liftComp [h : spec ⊂ₒ superSpec] (oa : OracleComp spec α) : OracleComp superSpec α :=
  simulate' (liftingOracle spec superSpec) () oa

lemma liftComp_def (oa : OracleComp spec α) : h.liftComp oa =
    simulate' (liftingOracle spec superSpec) () oa := rfl

lemma liftComp_pure (x : α) : h.liftComp (pure x : OracleComp spec α) = pure x :=
  simulate'_pure _ () x

lemma liftComp_query (i : ι₁) (t : spec.domain i) :
    h.liftComp (query i t) = h.monadLift (query i t) := rfl

lemma liftComp_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    h.liftComp (oa >>= ob) = h.liftComp oa >>= λ x ↦ h.liftComp (ob x) := by
  simp only [liftComp, simulate'_bind]
  rw [simulate_eq_map_simulate'_of_subsingleton _ _ _ ()]
  simp [simulate', Functor.map_map, Function.comp, map_eq_bind_pure_comp]

@[simp]
lemma evalDist_liftComp [spec.FiniteRange] [superSpec.FiniteRange] (oa : OracleComp spec α) :
    evalDist (h.liftComp oa) = evalDist oa := by
  sorry
  -- induction oa using OracleComp.inductionOn with
  -- | pure => simp [liftComp_pure]
  -- | query_bind i t oa hoa =>
  --     simp only [liftComp_bind, liftComp_query, evalDist_bind, evalDist_toFun, evalDist_query]
  --     exact congr_arg _ (funext hoa)

@[simp]
lemma support_liftComp (oa : OracleComp spec α) :
    (h.liftComp oa).support = oa.support := sorry
  -- Set.ext (mem_support_iff_of_evalDist_eq <| evalDist_liftComp oa)

@[simp]
lemma finSupport_liftComp [spec.DecidableEq] [superSpec.DecidableEq] [DecidableEq α]
    [spec.FiniteRange] [superSpec.FiniteRange]
    (oa : OracleComp spec α) : (h.liftComp oa).finSupport = oa.finSupport :=
  sorry
  -- Finset.ext (mem_finSupport_iff_of_evalDist_eq <| evalDist_liftComp oa)

@[simp]
lemma probOutput_liftComp [spec.FiniteRange] [superSpec.FiniteRange]
    (oa : OracleComp spec α) (x : α) : [= x | h.liftComp oa] = [= x | oa] := by
  simp only [probOutput_def, evalDist_liftComp]

@[simp]
lemma probEvent_liftComp [spec.FiniteRange] [superSpec.FiniteRange]
    (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    [p | h.liftComp oa] = [p | oa] := by
  simp only [probEvent_def, evalDist_liftComp]

end liftComp

instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (OracleComp spec) (OracleComp superSpec) where
  monadLift := liftComp

section instances

/-- The empty set of oracles is a subspec of any other oracle set.
We require `ι₁` to be inhabited to prevent the reflexive case.  -/
instance [Inhabited ι₁] : []ₒ ⊂ₒ spec where
  monadLift := λ q ↦ OracleQuery.isEmpty.elim q

/-- A computation with no oracles can be viewed as one with any other set of oracles. -/
instance [Inhabited ι₁] : MonadLift (OracleComp []ₒ) (OracleComp spec) where
  monadLift := liftComp

@[simp]
lemma coe_subSpec_empty_eq_liftComp {ι : Type} [Inhabited ι] {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp []ₒ α) : (oa : OracleComp spec α) = liftComp oa := rfl

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
