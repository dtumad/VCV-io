/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate
import VCVio.OracleComp.Constructions.UniformSelect

/-!
# Basic Constructions of Simulation Oracles

This file defines a number of basic simulation oracles, as well as operations to combine them.
-/

open OracleSpec OracleComp Prod Sum

namespace SimOracle

section compose

variable {spec₁ spec₂ specₜ : OracleSpec} {σ τ : Type}

/-- Given a simulation oracle `so` from `spec₁` to `spec₂` and a simulation oracle `so'` from
`spec₂` to a final target set of oracles `specₜ`, construct a new simulation oracle
from `spec₁` to `spec₂` by first substituting queries using `so`, and then further
substituting with the oracles in `so'`. -/
def compose (so : spec₁ →[σ]ₛₒ spec₂) (so' : spec₂ →[τ]ₛₒ specₜ) :
    spec₁ →[σ × τ]ₛₒ specₜ :=
  λ i t (s₁, s₂) ↦ do
    let ((t, s₁), s₂) ← simulate so' (so i t s₁) s₂
    return (t, (s₁, s₂))

infixl : 65 " ∘ₛₒ " => λ so' so ↦ compose so so'

variable (so : spec₁ →[σ]ₛₒ spec₂) (so' : spec₂ →[τ]ₛₒ specₜ)

@[simp]
lemma compose_apply (i : spec₁.ι) : (so' ∘ₛₒ so) i =
    λ t (s₁, s₂) ↦ (λ ((t, s₁), s₂) ↦ (t, (s₁, s₂))) <$>
      simulate so' (so i t s₁) s₂ := rfl

@[simp]
lemma simulate_compose (oa : OracleComp spec₁ α) :
    ∀ s : σ × τ, simulate (so' ∘ₛₒ so) oa s = do
      let ((x, s₁), s₂) ← simulate so' (simulate so oa s.1) s.2
      return (x, s₁, s₂) := by
  induction oa using OracleComp.inductionOn with
  | h_pure x => simp
  | h_query_bind i t oa hoa => simp [hoa, map_eq_bind_pure_comp]

/-- Composition of simulatation oracles is exactly composition of simulation calls. -/
@[simp]
lemma simulate'_compose (oa : OracleComp spec₁ α) :
    ∀ s : σ × τ, simulate' (so' ∘ₛₒ so) oa s =
      simulate' so' (simulate' so oa s.1) s.2 := by
  simp [simulate'_def, map_eq_bind_pure_comp]

end compose

variable {spec specₜ : OracleSpec} {σ τ : Type}

section maskState

/-- Substitute an equivalent type for the state of a simulation oracle, by using the equivalence
to move back and forth between the states as needed.
This can be useful when operations such like `simOracle.append` add on a state of type `Unit`.-/
def maskState (so : spec →[σ]ₛₒ specₜ) (e : σ ≃ τ) : spec →[τ]ₛₒ specₜ :=
  λ i t s ↦ map id e <$> so i t (e.symm s)

@[simp]
lemma maskState_apply (so : spec →[σ]ₛₒ specₜ) (e : σ ≃ τ) (i : spec.ι) :
    so.maskState e i = λ t s ↦ map id e <$> so i t (e.symm s) := rfl

/-- Masking a `Subsingleton` state has no effect, since the new state elements look the same. -/
@[simp]
lemma maskState_subsingleton [Subsingleton σ] (so : so →[σ]ₛₒ specₜ) (e : σ ≃ σ) :
    so.maskState e = so := by
  have he : ⇑e = id := funext (λ _ ↦ Subsingleton.elim _ _)
  have he' : ⇑e.symm = id := funext (λ _ ↦ Subsingleton.elim _ _)
  refine funext (λ i ↦ funext (λ t ↦ ?_))
  simp only [maskState_apply, he, he', map_id, id_map, id]

@[simp]
lemma simulate_maskState (so : spec →[σ]ₛₒ specₜ) (e : σ ≃ τ) (oa : OracleComp spec α) :
    ∀ s : τ, simulate (so.maskState e) oa s = map id e <$> simulate so oa (e.symm s) := by
  induction oa using OracleComp.inductionOn with
  | h_pure x => simp
  | h_query_bind i t oa hoa => simp [hoa, map_eq_bind_pure_comp]

/-- Masking the state doesn't affect the first output of a computation. -/
@[simp]
lemma simulate'_maskState (so : spec →[σ]ₛₒ specₜ) (e : σ ≃ τ) (oa : OracleComp spec α) :
    ∀ s : τ, simulate' (so.maskState e) oa s = simulate' so oa (e.symm s) := by
  simp only [simulate'_def, simulate_maskState, fst_map_prod_map, id_eq, implies_true]

end maskState

end SimOracle

/-- "Simulate" a computation using the original oracles by "replacing" queries with queries.
This operates as an actual identity for `simulate'`, in that we get an exact equality
between the new and original computation.
This can be useful especially with `SimOracle.append`, in order to simulate a single oracle
in a larger set of oracles, leaving the behavior of other oracles unchanged.

This is importantly different than `unifOracle`, which preserves probabilities but
changes the target oracle spec to `unifSpec` by explicitly choosing outputs randomly.

The relevant spec can usually be inferred automatically, so we leave it implicit. -/
def idOracle {spec : OracleSpec} : spec →[Unit]ₛₒ spec :=
  λ i t () ↦ (·, ()) <$> query i t

namespace idOracle

variable (spec : OracleSpec)

@[simp]
lemma apply_eq (i : spec.ι) : idOracle i = λ t () ↦ ((., ())) <$> query i t := rfl

example (oa : OracleComp spec α) (f : α → β)
  (ob : β → OracleComp spec γ) :
  (f <$> oa) >>= ob = oa >>= (ob ∘ f) := by
  exact seq_bind_eq oa

@[simp]
lemma simulate'_eq (oa : OracleComp spec α) :
    simulate' idOracle oa = λ _ ↦ oa := by
  refine funext (λ () ↦ ?_)
  induction oa using OracleComp.inductionOn with
  | h_pure x => rfl
  | h_query_bind i t oa hoa =>
      simp [Functor.map_map, Function.comp, hoa, seq_bind_eq]

@[simp]
lemma simulate_eq (oa : OracleComp spec α) :
    simulate idOracle oa = λ _ ↦ ((·, ())) <$> oa := by
  refine funext (λ () ↦ ?_)
  rw [simulate_eq_map_simulate', simulate'_eq]

end idOracle

/-- Simulation oracle for replacing queries with uniform random selection, using `unifSpec`.
The resulting computation is still identical under `evalDist`.
The relevant `OracleSpec` can usually be inferred automatically, so we leave it implicit. -/
def unifOracle {spec : OracleSpec} [∀ i, SelectableType (spec.range i)] :
    spec →[PUnit]ₛₒ unifSpec :=
  λ i _ _ ↦ (·, ()) <$> $ᵗ (spec.range i)

namespace unifOracle

variable {spec : OracleSpec} [∀ i, SelectableType (spec.range i)]

@[simp]
lemma apply_eq (i : spec.ι) : unifOracle i = λ _ _ ↦ (., ()) <$> $ᵗ (spec.range i) := rfl

@[simp]
lemma evalDist_simulate (oa : OracleComp spec α) (u : Unit) :
    evalDist (simulate unifOracle oa u) = (evalDist oa).map ((., ())) := by
  revert u
  induction oa using OracleComp.inductionOn with
  | h_pure => simp only [simulate_pure, evalDist_pure, PMF.pure_map, forall_const]
  | h_query_bind i t oa hoa => sorry --simp [PMF.map, hoa]

@[simp]
lemma evalDist_simulate' (oa : OracleComp spec α) (u : PUnit) :
    evalDist (simulate' unifOracle oa u) = evalDist oa := sorry
  -- by simpa [PMF.map_comp, Function.comp] using PMF.map_id (evalDist oa)

@[simp]
lemma probOutput_simulate (oa : OracleComp spec α) (u : Unit) (z : α × Unit) :
    [= z | simulate unifOracle oa u] = [= z.1 | oa] := by
  rw [simulate_eq_map_simulate']
  sorry

@[simp]
lemma probOutput_simulate' (oa : OracleComp spec α) (u : Unit) (x : α) :
    [= x | simulate' unifOracle oa u] = [= x | oa] := by
  sorry

@[simp]
lemma probEvent_simulate (oa : OracleComp spec α) (u : Unit) (p : α × Unit → Prop) :
    [p | simulate unifOracle oa u] = [λ x ↦ p (x, ()) | oa] := by
  sorry

@[simp]
lemma probEvent_simulate' (oa : OracleComp spec α) (u : Unit) (p : α → Prop) :
    [p | simulate' unifOracle oa u] = [p | oa] := by
  sorry

end unifOracle
