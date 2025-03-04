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

variable {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β γ : Type u}

namespace QueryImpl

section compose

variable {m : Type u → Type v} [AlternativeMonad m] [LawfulAlternative m]

/-- Given an implementation of `spec` in terms of a new set of oracles `spec'`,
and an implementation of `spec'` in terms of arbitrary `m`, implement `spec` in terms of `m`. -/
def compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec')) :
    QueryImpl spec m where
  impl q := simulateQ so' (so.impl q)

infixl : 65 "∘ₛ" => QueryImpl.compose

@[simp]
lemma apply_compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec'))
    (q : OracleQuery spec α) : (so' ∘ₛ so).impl q = simulateQ so' (so.impl q) := rfl

@[simp]
lemma simulateQ_compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec'))
    (oa : OracleComp spec α) : simulateQ (so' ∘ₛ so) oa = simulateQ so' (simulateQ so oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa hoa => simp [hoa]
  | failure => simp

end compose

section equivState

variable {σ τ : Type u}

/-- Substitute an equivalent type for the state of a simulation oracle, by using the equivalence
to move back and forth between the states as needed.
This can be useful when operations such like `simOracle.append` add on a state of type `Unit`.
TODO: this should really exist on the `StateT` level probably instead. -/
def equivState (so : QueryImpl spec (StateT σ (OracleComp spec'))) (e : σ ≃ τ) :
    QueryImpl spec (StateT τ (OracleComp spec')) where
  impl q s := map id e <$> so.impl q (e.symm s)

variable (so : QueryImpl spec (StateT σ (OracleComp spec'))) (e : σ ≃ τ)

@[simp]
lemma equivState_apply (q : OracleQuery spec α) :
    (so.equivState e).impl q = λ s ↦ map id e <$> so.impl q (e.symm s) := rfl

/-- Masking a `Subsingleton` state has no effect, since the new state elements look the same. -/
@[simp]
lemma equivState_subsingleton [Subsingleton σ] (e : σ ≃ σ) :
    so.equivState e = so :=
  QueryImpl.ext' λ _ ↦ by simp [Equiv.Perm.coe_subsingleton e, Equiv.Perm.coe_subsingleton e.symm]

@[simp]
lemma equivState_equivState : (so.equivState e).equivState e.symm = so :=
  QueryImpl.ext' λ q ↦ by simp [Prod.map]

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

end QueryImpl

/-- Simulate a computation using the original oracles by "replacing" queries with queries.
This operates as an actual identity for `simulate'`, in that we get an exact equality
between the new and original computation.
This can be useful especially with `SimOracle.append`, in order to simulate a single oracle
in a larger set of oracles, leaving the behavior of other oracles unchanged.
The relevant spec can usually be inferred automatically, so we leave it implicit. -/
def idOracle : QueryImpl spec (OracleComp spec) where
  impl q := OracleComp.lift q

namespace idOracle

@[simp]
lemma apply_eq (q : OracleQuery spec α) : idOracle.impl q = q := rfl

@[simp]
lemma simulateQ_eq (oa : OracleComp spec α) :
    simulateQ idOracle oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind i t oa hoa => simp [hoa]
  | failure => rfl

end idOracle

/-- Simulation oracle for replacing queries with uniform random selection, using `unifSpec`.
The resulting computation is still identical under `evalDist`.
The relevant `OracleSpec` can usually be inferred automatically, so we leave it implicit. -/
def unifOracle [∀ i, SelectableType (spec.range i)] :
    QueryImpl spec ProbComp where
  impl | query i _ => $ᵗ spec.range i

namespace unifOracle

variable [∀ i, SelectableType (spec.range i)] {α : Type}

@[simp]
lemma apply_eq (q : OracleQuery spec α) :
    unifOracle.impl q = match q with | query i t => $ᵗ spec.range i :=
  match q with | query i t => rfl

@[simp]
lemma evalDist_simulateQ [spec.FiniteRange] (oa : OracleComp spec α) :
    evalDist (simulateQ unifOracle oa) = evalDist oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa hoa => simp [hoa, Function.comp_def]
  | failure => simp

@[simp]
lemma support_simulateQ (oa : OracleComp spec α) :
    (simulateQ unifOracle oa).support = oa.support := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa hoa => simp [hoa, Function.comp_def]
  | failure => simp

@[simp]
lemma finSupport_simulateQ [spec.FiniteRange] [spec.DecidableEq] [DecidableEq α]
    (oa : OracleComp spec α) : (simulateQ unifOracle oa).finSupport = oa.finSupport := by
  simp [finSupport_eq_iff_support_eq_coe, Set.ext_iff]

@[simp]
lemma probOutput_simulateQ [spec.FiniteRange] (oa : OracleComp spec α) (x : α) :
    [= x | simulateQ unifOracle oa] = [= x | oa] :=
  probOutput_congr rfl (evalDist_simulateQ oa)

@[simp]
lemma probEvent_simulateQ [spec.FiniteRange] (oa : OracleComp spec α)
    (p : α → Prop) [DecidablePred p] :
    [p | simulateQ unifOracle oa] = [p | oa] := by
  refine probEvent_congr (fun _ => Iff.rfl) (evalDist_simulateQ oa)

end unifOracle

/-- Simulate a computation by having each oracle return the default value of the query output type
for all queries. This gives a way to run arbitrary computations to get *some* output.
Mostly useful in some existence proofs, not usually used in an actual implementation.
NOTE: output monad should really be `Id` but doesn't exist currently. -/
def defaultOracle [spec.FiniteRange] : QueryImpl spec (OracleComp []ₒ) where
  impl | q => do return q.defaultOutput

namespace defaultOracle

variable [FiniteRange spec]

@[simp]
lemma apply_eq (q : OracleQuery spec α) :
    defaultOracle.impl q = return q.defaultOutput := rfl

@[simp]
lemma simulateQ_eq (oa : OracleComp spec α) :
    simulateQ defaultOracle oa = oa.defaultResult.getM := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [defaultResult, Option.getM]
  | query_bind i t oa hoa => simp [hoa]; rfl
  | failure => simp [defaultResult, Option.getM]

end defaultOracle
