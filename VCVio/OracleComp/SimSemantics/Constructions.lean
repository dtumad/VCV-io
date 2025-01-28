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

universe u v w

lemma StateT.liftM_def {m : Type u → Type v} [Monad m] {σ : Type u} {α : Type u}
    (x : m α) : (x : StateT σ m α) = StateT.lift x := rfl

lemma OptionT.liftM_def {m : Type u → Type v} [Monad m] {α : Type u}
    (x : m α) : (x : OptionT m α) = OptionT.lift x := rfl

namespace SimOracle

section compose

variable {ι₁ ι₂ ιₜ : Type} {spec₁ : OracleSpec ι₁}
  {spec₂ : OracleSpec ι₂} {specₜ : OracleSpec ιₜ} {α β σ τ : Type}

/-- Given a simulation oracle `so` from `spec₁` to `spec₂` and a simulation oracle `so'` from
`spec₂` to a final target set of oracles `specₜ`, construct a new simulation oracle
from `spec₁` to `spec₂` by first substituting queries using `so`, and then further
substituting with the oracles in `so'`. -/
def compose (so : spec₁ →[σ]ₛₒ spec₂) (so' : spec₂ →[τ]ₛₒ specₜ) :
    spec₁ →[σ × τ]ₛₒ specₜ where
  impl | q, (s₁, s₂) => do
    let ((t, s₁'), s₂') ← simulate so' s₂ (so.impl q s₁)
    return (t, (s₁', s₂'))

infixl : 65 " ∘ₛₒ " => λ so' so ↦ compose so so'

variable (so : spec₁ →[σ]ₛₒ spec₂) (so' : spec₂ →[τ]ₛₒ specₜ)

@[simp]
lemma compose_apply (q : OracleQuery spec₁ α) : (so.compose so').impl q =
    (λ (s₁, s₂) ↦ (do
      let ((t, s₁'), s₂') ← simulate so' s₂ (so.impl q s₁)
      return (t, (s₁', s₂')))) := rfl

@[simp]
lemma simulate_compose (oa : OracleComp spec₁ α) :
    ∀ s : σ × τ, simulate (so.compose so') s oa = do
      let ((x, s₁), s₂) ← simulate so' s.2 (simulate so s.1 oa)
      return (x, (s₁, s₂)) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa hoa => simp [hoa, map_eq_bind_pure_comp]
  | failure => simp

/-- Composition of simulatation oracles is exactly composition of simulation calls. -/
@[simp]
lemma simulate'_compose (oa : OracleComp spec₁ α) :
    ∀ s : σ × τ, simulate' (so.compose so') s oa =
      simulate' so' s.2 (simulate' so s.1 oa):= by
  simp [simulate'_def, map_eq_bind_pure_comp]

end compose

section maskState

variable {ι ιₜ : Type} {spec : OracleSpec ι} {specₜ : OracleSpec ιₜ} {α β σ τ : Type}

/-- Substitute an equivalent type for the state of a simulation oracle, by using the equivalence
to move back and forth between the states as needed.
This can be useful when operations such like `simOracle.append` add on a state of type `Unit`.-/
def maskState (so : spec →[σ]ₛₒ specₜ) (e : σ ≃ τ) : spec →[τ]ₛₒ specₜ where
  impl q s := map id e <$> so.impl q (e.symm s)

@[simp]
lemma maskState_apply (so : spec →[σ]ₛₒ specₜ) (e : σ ≃ τ) (q : OracleQuery spec α) :
    (so.maskState e).impl q = λ s ↦ map id e <$> so.impl q (e.symm s) := rfl

/-- Masking a `Subsingleton` state has no effect, since the new state elements look the same. -/
@[simp]
lemma maskState_subsingleton [Subsingleton σ] (so : spec →[σ]ₛₒ specₜ) (e : σ ≃ σ) :
    SimOracle.maskState so e = so := by
  have he : ⇑e = id := funext (λ _ ↦ Subsingleton.elim _ _)
  have he' : ⇑e.symm = id := funext (λ _ ↦ Subsingleton.elim _ _)
  sorry
  -- refine funext (λ i ↦ funext (λ t ↦ ?_))
  -- simp only [maskState_apply, he, he', map_id, id_map, id]

@[simp]
lemma simulate_maskState (so : spec →[σ]ₛₒ specₜ) (e : σ ≃ τ) (s : τ) (oa : OracleComp spec α) :
    simulate (so.maskState e) s oa = map id e <$> simulate so (e.symm s) oa := by
  revert s; induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa hoa => simp [hoa, map_eq_bind_pure_comp]
  | failure => simp

/-- Masking the state doesn't affect the main output of a simulation. -/
@[simp]
lemma simulate'_maskState (so : spec →[σ]ₛₒ specₜ) (e : σ ≃ τ) (s : τ) (oa : OracleComp spec α) :
    simulate' (so.maskState e) s oa = simulate' so (e.symm s) (oa) := by
  simp only [simulate'_def, simulate_maskState, fst_map_prod_map, CompTriple.comp_eq]
  sorry

end maskState

end SimOracle

/-- Given a indexed computation that computes an oracle output from an oracle input,
construct a simulation oracle that responds to the queries with that computation.

This assumes no shared state across responses, so we use `Unit` as the state.
`maskState` is often useful to hide this when appending or composing this. -/
def statelessOracle {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : {α : Type} → OracleQuery spec α → OracleComp spec' α) :
    SimOracle spec spec' Unit where
  impl q := f q

namespace statelessOracle

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
  (f : {α : Type} → OracleQuery spec α → OracleComp spec' α) {α : Type}

@[simp]
lemma apply_eq (q : OracleQuery spec α) : (statelessOracle f).impl q = f q := rfl

end statelessOracle

/-- Simulate a computation using the original oracles by "replacing" queries with queries.
This operates as an actual identity for `simulate'`, in that we get an exact equality
between the new and original computation.

This can be useful especially with `SimOracle.append`, in order to simulate a single oracle
in a larger set of oracles, leaving the behavior of other oracles unchanged.
The relevant spec can usually be inferred automatically, so we leave it implicit. -/
def idOracle {ι : Type} {spec : OracleSpec ι} : spec →[Unit]ₛₒ spec :=
  statelessOracle (λ q ↦ q)

namespace idOracle

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

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
lemma simulate'_eq (u : Unit) (oa : OracleComp spec α) :
    simulate' idOracle u oa = oa := by
  simp [simulate']

@[simp]
lemma simulate_eq (u : Unit) (oa : OracleComp spec α) :
    simulate idOracle u oa = (·, ()) <$> oa := by
  rw [simulate_eq_map_simulate', simulate'_eq]

end idOracle

/-- Simulation oracle for replacing queries with uniform random selection, using `unifSpec`.
The resulting computation is still identical under `evalDist`.
The relevant `OracleSpec` can usually be inferred automatically, so we leave it implicit. -/
def unifOracle {ι : Type} {spec : OracleSpec ι} [∀ i, SelectableType (spec.range i)] :
    SimOracle spec unifSpec Unit :=
  statelessOracle λ (query i _) ↦ $ᵗ spec.range i

namespace unifOracle

variable {ι : Type} {spec : OracleSpec ι} [∀ i, SelectableType (spec.range i)] {α β : Type}

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
    evalDist (simulate unifOracle u oa) = (evalDist oa).map (Option.map (·, ())) := by
  rw [simulate_eq_map_simulate', evalDist_map, evalDist_simulate' oa u]
  simp [Subsingleton.elim _ (), map_eq_bind_pure_comp, PMF.map]
  sorry

@[simp]
lemma support_simulate (oa : OracleComp spec α) (u : Unit) :
    (simulate unifOracle u oa).support = {z | z.1 ∈ oa.support} := by
  sorry

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
def defaultOracle {ι : Type} {spec : OracleSpec ι} [spec.FiniteRange] :
    SimOracle spec []ₒ Unit :=
  statelessOracle λ q ↦ return q.defaultOutput

-- namespace defaultOracle

-- variable {ι : Type} {spec : OracleSpec ι} [spec.FiniteRange] {α : Type}

-- @[simp]
-- lemma apply_eq (q : OracleQuery spec α) :
--     defaultOracle.impl q = return q.defaultOutput := rfl

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

-- end defaultOracle
