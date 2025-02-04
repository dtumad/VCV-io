/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.DistSemantics.Prod

/-!
# Basic Constructions of Simulation Oracles

This file defines a number of basic simulation oracles, as well as operations to combine them.
-/

open OracleSpec OracleComp Prod Sum

universe u₁ u₂ uₜ v₁ v₂ vₜ u u' v v' w w' w₁ w₂ wₜ

variable {ι ι₁ ι₂ ιₜ : Type*} {spec : OracleSpec ι}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {specₜ : OracleSpec ιₜ} {α β γ σ τ : Type u}

namespace SimOracle

section compose

-- If `m` can be used to map between monads
class CompatibleTransform (m : (Type u → Type v) → Type u → Type w)
  (m' : (Type u → Type v) → Type u → Type v) where
  mapUnder {n n' : Type u → Type v} [Monad n']
    {α : Type u} (f : {α : Type u} → n α → m n' α)
    (x : m' n α) : m (m' n') α

instance : CompatibleTransform (StateT τ) (StateT σ) where
  mapUnder f x := StateT.mk fun s => StateT.mk fun t =>
    (fun ((x, t), s) => ((x, s), t)) <$> (f (x t)).run s

-- This version is really not very nice
def compose' {ι₁ : Type u₁} {ι₂ : Type u₂} {ιₜ : Type u₂}
    {spec₁ : OracleSpec.{u₁,v} ι₁} {spec₂ : OracleSpec.{u₂,v} ι₂}
    {specₜ : OracleSpec.{u₂,v} ιₜ}

    {T : (Type v → Type (max u₂ (v + 1) v)) → Type v → Type w}
    [Alternative (T (OracleComp specₜ))]
    [Monad (T (OracleComp specₜ))]

    {U : (Type v → Type (max u₂ (v + 1))) → Type v → Type (max u₂ (v + 1))}
    [Alternative (U (OracleComp spec₂))]
    [Monad (U (OracleComp spec₂))]

    [Alternative ((T ∘ U) (OracleComp spec₂))]
    [Monad ((T ∘ U) (OracleComp spec₂))]
    [h : CompatibleTransform T U]

    (so' : SimOracle' spec₂ specₜ T)
    (so : SimOracle' spec₁ spec₂ U) :
    SimOracle' spec₁ specₜ (T ∘ U) where
    impl q := h.mapUnder (m := T) (m' := U)
      (n := OracleComp spec₂) (n' := OracleComp specₜ)
      (λ {α} ↦ simulateT' (α := α) so') (so.impl q)

infixl : 65 "∘ₛ'" => SimOracle.compose'

-- Class for monad transformers that allow lifting functions on base monads.
class MonadTransform (m : (Type u → Type v) → Type u → Type w) where
    mapUnder {n n' : Type u → Type v} [Monad n'] {α : Type u}
      (f : {α : Type u} → n α → n' α) (x : m n α) : m n' α

-- Unwrap the result, apply the map, rewrap
instance : MonadTransform OptionT where
  mapUnder f x := OptionT.mk (f x.run)

-- Get the state, apply the map, return the state
instance : MonadTransform (StateT σ) where
  mapUnder f x := StateT.mk fun s => f (x.run s)

def composeState'' (so' : QueryImpl spec₂ (StateT τ (OracleComp specₜ)))
    (so : QueryImpl spec₁ (StateT σ (OracleComp spec₂))) :
    QueryImpl spec₁ (StateT σ (StateT τ (OracleComp specₜ))) where
  impl q := StateT.mk fun s =>
    StateT.mk (simulateQ so' ((so.impl q).run s)).run

/-- Given a simulation oracle `so` from `spec₁` to `spec₂` and a simulation oracle `so'` from
`spec₂` to a final target set of oracles `specₜ`, construct a new simulation oracle
from `spec₁` to `spec₂` by first substituting queries using `so`, and then further
substituting with the oracles in `so'`.
NOTE: One of few constructions that work better with `simulate` than `simulateT`. -/
def compose (so' : SimOracle spec₂ specₜ τ) (so : SimOracle spec₁ spec₂ σ) :
    SimOracle spec₁ specₜ (σ × τ) where
  impl | q, (s₁, s₂) => do
    (λ ((t, s₁'), s₂') ↦ (t, (s₁', s₂'))) <$>
      simulate so' s₂ (so.impl q s₁)

infixl : 65 "∘ₛ" => SimOracle.compose

variable (so : SimOracle spec₁ spec₂ σ) (so' : SimOracle spec₂ specₜ τ)

@[simp]
lemma impl_compose (q : OracleQuery spec₁ α) : (so' ∘ₛ so).impl q = λ (s₁, s₂) ↦
    (do (λ ((t, s₁'), s₂') ↦ (t, (s₁', s₂'))) <$> simulate so' s₂ (so.impl q s₁)) := rfl

-- @[simp]
-- lemma simulateT_compose (oa : OracleComp spec₁ α) :
--     simulateT (so' ∘ₛ so) oa = StateT.mk λ s ↦ (do
--       (λ ((t, s₁'), s₂') ↦ (t, (s₁', s₂'))) <$>
--         (simulateT so' ((simulateT so oa).run s.1).run s.2)) := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => {
--     -- refine StateT.ext ?_
--     -- simp only [simulateT_pure, StateT.run_pure, OptionT.run_pure, FreeMonad.monad_pure_def]
--     rfl
--     -- simp only [simulateT_pure, StateT.run_pure, OptionT.run_pure,
--     --   map_eq_bind_pure_comp, StateT.ext_iff, StateT.run_mk, pure_eq_bind_iff, Function.comp_apply,
--     --   pure_inj, Prod.mk.injEq, Prod.exists, Prod.forall]
--   }
--   | query_bind i t oa hoa => {
--       -- refine StateT.ext ?_
--       -- simp [Function.comp_def]
--       simp [hoa, Function.comp_def]
--       refine StateT.ext ?_
--       simp [map_eq_bind_pure_comp, StateT.run, StateT.mk,
--         OptionT.run]
--       intro s₁ s₂


--   }
--   | failure => rfl

@[simp]
lemma simulate_compose (oa : OracleComp spec₁ α) (s : σ × τ) :
    simulate (so' ∘ₛ so) s oa = do
      let ((x, s₁), s₂) ← simulate so' s.2 (simulate so s.1 oa)
      return (x, (s₁, s₂)) := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa hoa =>
      simp [hoa, map_eq_bind_pure_comp]
      sorry
  | failure => simp

/-- Composition of simulatation oracles is exactly composition of simulation calls. -/
@[simp]
lemma simulate'_compose (oa : OracleComp spec₁ α) :
    ∀ s : σ × τ, simulate' (so' ∘ₛ so) s oa =
      simulate' so' s.2 (simulate' so s.1 oa):= by
  simp [simulate'_def, map_eq_bind_pure_comp]

end compose

section equivState

def equivState' (so : SimOracle' spec specₜ (StateT σ)) (e : σ ≃ τ) :
    SimOracle' spec specₜ (StateT τ) where
  impl q s := map id e <$> so.impl q (e.symm s)

def equivState'' (so : QueryImpl spec (StateT σ (OracleComp specₜ))) (e : σ ≃ τ) :
    QueryImpl spec (StateT τ (OracleComp specₜ)) where
  impl q s := map id e <$> so.impl q (e.symm s)

/-- Substitute an equivalent type for the state of a simulation oracle, by using the equivalence
to move back and forth between the states as needed.
This can be useful when operations such like `simOracle.append` add on a state of type `Unit`.
TODO: this should really exist on the `StateT` level probably. -/
def equivState (so : SimOracle spec specₜ σ) (e : σ ≃ τ) :
    SimOracle spec specₜ τ where
  impl q s := map id e <$> so.impl q (e.symm s)

variable (so : SimOracle spec specₜ σ) (e : σ ≃ τ)

@[simp]
lemma equivState_apply (q : OracleQuery spec α) :
    (so.equivState e).impl q = λ s ↦ map id e <$> so.impl q (e.symm s) := rfl

/-- Masking a `Subsingleton` state has no effect, since the new state elements look the same. -/
@[simp]
lemma equivState_subsingleton [Subsingleton σ] (e : σ ≃ σ) :
    so.equivState e = so :=
  SimOracle.ext' λ _ ↦ by simp [Equiv.Perm.coe_subsingleton e, Equiv.Perm.coe_subsingleton e.symm]

@[simp]
lemma equivState_equivState : (so.equivState e).equivState e.symm = so :=
  SimOracle.ext' λ q ↦ by simp [Prod.map]

-- lemma simulateT_equivState (oa : OracleComp spec α) :
--     simulateT (so.equivState e) oa =
--       StateT.mk λ s ↦ map id e <$> (simulateT so oa).run (e.symm s) := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => {
--     simp
--   }
--   | query_bind i t oa hoa => {
--     sorry
--   }
--   | failure => {
--     rfl
--   }

@[simp]
lemma simulate_equivState (s : τ) (oa : OracleComp spec α) :
    simulate (so.equivState e) s oa = map id e <$> simulate so (e.symm s) oa := by
  revert s; induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa hoa =>
      intro s
      simp [hoa, map_eq_bind_pure_comp, StateT.run]

      sorry
  | failure => simp

/-- Masking the state doesn't affect the main output of a simulation. -/
@[simp]
lemma simulate'_equivState (s : τ) (oa : OracleComp spec α) :
    simulate' (so.equivState e) s oa = simulate' so (e.symm s) (oa) := by
  simp only [StateT.run'_eq, simulate_equivState, Functor.map_map, map_fst, id_eq]

end equivState

end SimOracle

-- This isn't really good naming anymore with the changes
def statelessOracle' (f : {α : Type u} → OracleQuery spec α → OracleComp specₜ α) :
    SimOracle' spec specₜ id where
  impl q := f q

def statelessOracle'' (f : {α : Type u} → OracleQuery spec α → OracleComp specₜ α) :
    QueryImpl spec (OracleComp specₜ) where
  impl q := f q

/-- Given a indexed computation that computes an oracle output from an oracle input,
construct a simulation oracle that responds to the queries with that computation.

This assumes no shared state across responses, so we use `Unit` as the state.
`equivState` is often useful to hide this when appending or composing this. -/
def statelessOracle (f : {α : Type u} → OracleQuery spec α → OracleComp specₜ α) :
    SimOracle spec specₜ PUnit where
  impl q := StateT.lift (f q)

namespace statelessOracle

variable (f : {α : Type u} → OracleQuery spec α → OracleComp specₜ α)

@[simp]
lemma apply_eq (q : OracleQuery spec α) : (statelessOracle f).impl q = f q := rfl

end statelessOracle

def idOracle'' : QueryImpl spec (OracleComp spec) :=
  statelessOracle'' OracleComp.lift

def idOracle' : SimOracle' spec spec id :=
  statelessOracle' OracleComp.lift

/-- Simulate a computation using the original oracles by "replacing" queries with queries.
This operates as an actual identity for `simulate'`, in that we get an exact equality
between the new and original computation.
This can be useful especially with `SimOracle.append`, in order to simulate a single oracle
in a larger set of oracles, leaving the behavior of other oracles unchanged.
The relevant spec can usually be inferred automatically, so we leave it implicit. -/
def idOracle : SimOracle spec spec PUnit :=
  statelessOracle fun q => q

namespace idOracle

@[simp]
lemma apply_eq (q : OracleQuery spec α) : idOracle.impl q = q := rfl

@[simp]
lemma simulateT_eq (oa : OracleComp spec α) :
    simulateT idOracle oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind i t oa hoa =>
      simp [simulateT] at hoa
      simp [simulateT, hoa]
      rfl
  | failure => rfl

@[simp]
lemma simulate'_eq (u : PUnit) (oa : OracleComp spec α) :
    simulate' idOracle u oa = oa := by
  simp [simulate']

@[simp]
lemma simulate_eq (u : PUnit) (oa : OracleComp spec α) :
    simulate idOracle u oa = (·, PUnit.unit) <$> oa := by
  rw [simulate_eq_map_simulate', simulate'_eq]

end idOracle

def unifOracle'' [∀ i, SelectableType (spec.range i)] :
    QueryImpl spec (OracleComp unifSpec) :=
  statelessOracle'' fun (query i _) => $ᵗ spec.range i

/-- Simulation oracle for replacing queries with uniform random selection, using `unifSpec`.
The resulting computation is still identical under `evalDist`.
The relevant `OracleSpec` can usually be inferred automatically, so we leave it implicit. -/
def unifOracle [∀ i, SelectableType (spec.range i)] :
    SimOracle spec unifSpec PUnit :=
  statelessOracle fun (query i _) => $ᵗ spec.range i

namespace unifOracle

variable [∀ i, SelectableType (spec.range i)] {α : Type}

@[simp]
lemma apply_eq (q : OracleQuery spec α) :
    unifOracle.impl q = match q with | query i t => $ᵗ spec.range i :=
  match q with | query i t => rfl

@[simp]
lemma evalDist_simulate' [spec.FiniteRange] (oa : OracleComp spec α) (u : Unit) :
    evalDist (simulate' unifOracle u oa) = evalDist oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => erw [simulate'_pure, evalDist_pure]
  | query_bind i t oa hoa =>
    rw [simulate'_bind, evalDist_bind, Function.comp_def]
    simp at hoa
    simp [hoa, StateT.liftM_def, StateT.lift, Function.comp_def]
  | failure => erw [simulate'_failure, evalDist_failure]

@[simp]
lemma evalDist_simulate [spec.FiniteRange] (oa : OracleComp spec α) (u : Unit) :
    evalDist (simulate unifOracle u oa) = ((·, ())) <$> (evalDist oa) := by
  rw [simulate_eq_map_simulate', evalDist_map, evalDist_simulate' oa u]

@[simp]
lemma support_simulate (oa : OracleComp spec α) (u : Unit) :
    (simulate unifOracle u oa).support = {z | z.1 ∈ oa.support} := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [Set.ext_iff]
  | query_bind i t oa hoa => simp [hoa, Set.ext_iff]
  | failure => simp

@[simp]
lemma support_simulate' (oa : OracleComp spec α) (u : Unit) :
    (simulate' unifOracle u oa).support = oa.support := by
  simp [simulate', Set.ext_iff]

@[simp]
lemma finSupport_simulate [spec.FiniteRange] [spec.DecidableEq]
    [DecidableEq α] (oa : OracleComp spec α) (u : Unit) :
    (simulate unifOracle u oa).finSupport = oa.finSupport.image (·, ()) := by
  simp [finSupport_eq_iff_support_eq_coe, Set.ext_iff]

@[simp]
lemma finSupport_simulate' [spec.FiniteRange] [spec.DecidableEq]
    [DecidableEq α] (oa : OracleComp spec α) (u : Unit) :
    (simulate' unifOracle u oa).finSupport = oa.finSupport := by
  simp [simulate'_def, Finset.ext_iff]

@[simp]
lemma probOutput_simulate' [spec.FiniteRange] (oa : OracleComp spec α) (u : Unit) (x : α) :
    [= x | simulate' unifOracle u oa] = [= x | oa] :=
  probOutput_congr rfl (evalDist_simulate' oa u)

@[simp]
lemma probOutput_simulate [spec.FiniteRange] (oa : OracleComp spec α)
    (u : Unit) (z : α × Unit) : [= z | simulate unifOracle u oa] = [= z.1 | oa] := by
  rw [simulate_eq_map_simulate', probOutput_map_eq_single z.1]
  · exact probOutput_simulate' oa u z.1
  · simp [Prod.eq_iff_fst_eq_snd_eq]
  · simp only [PUnit.default_eq_unit]

@[simp]
lemma probEvent_simulate [spec.FiniteRange] (oa : OracleComp spec α) (u : Unit)
    (p : α × Unit → Prop) [DecidablePred p] :
    [p | simulate unifOracle u oa] = [λ x ↦ p (x, ()) | oa] := by
  rw [simulate_eq_map_simulate', probEvent_map]
  refine probEvent_congr ?_ (evalDist_simulate' oa u)
  simp only [PUnit.default_eq_unit, Function.comp_apply, implies_true]

@[simp]
lemma probEvent_simulate' [spec.FiniteRange] (oa : OracleComp spec α) (u : Unit)
    (p : α → Prop) [DecidablePred p] :
    [p | simulate' unifOracle u oa] = [p | oa] :=
  probEvent_congr (λ _ ↦ Iff.rfl) <| evalDist_simulate' oa u

end unifOracle

/-- Simulate a computation by having each oracle return the default value of the query output type
for all queries. This gives a way to run arbitrary computations to get *some* output.
Mostly useful in some existence proofs, not usually used in an actual implementation. -/
def defaultOracle [spec.FiniteRange] : SimOracle spec []ₒ PUnit :=
  statelessOracle fun q => return q.defaultOutput

namespace defaultOracle

variable [FiniteRange spec]

@[simp]
lemma apply_eq (q : OracleQuery spec α) :
    defaultOracle.impl q = return q.defaultOutput := rfl

-- @[simp]
-- lemma simulate_eq (u : Unit) (oa : OracleComp spec α) :
--     simulate defaultOracle u oa = (oa.defaultResult.map (·, ())).getM := by
--   sorry
--   -- induction oa using OracleComp.inductionOn with
--   -- | h_pure x => simp only [simulate_eq_map_simulate', PUnit.default_eq_unit,
--   --     simulate'_pure, map_pure, defaultResult]
--   -- | h_queryBind i t oa hoa => simp only [simulate_bind, simulate_query, apply_eq,
  -- hoa, pure_bind,
--   --     defaultResult, OracleComp.bind'_eq_bind]

-- @[simp]
-- lemma simulate'_eq (u : Unit) (oa : OracleComp spec α) :
--     simulate' defaultOracle u oa = oa.defaultResult.getM := by
--   simp only [simulate'_def, simulate_eq, map_pure]
--   sorry

end defaultOracle
