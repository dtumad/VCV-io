/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.GenerateSeed
import VCVio.OracleComp.SimSemantics.QueryTracking.LoggingOracle
import VCVio.OracleComp.Coercions.Append

/-!
# Forking Lemma

-/

open OracleSpec OracleComp Option ENNReal

-- structure ForkAdv {ι : Type} (spec : OracleSpec ι) (α β : Type) (i : ι)
--     extends SecAdv spec α β where
--   chooseFork : α → β → Option (Fin (queryBound i + 1))

-- namespace ForkAdv

-- variable {spec : OracleSpec} [∀ j, SelectableType (spec.range j)]
--   [unifSpec ⊂ₒ spec] {α β : Type} {i : spec.ι}

-- def seedAndRun (adv : ForkAdv spec α β i)
--     (x : α) (initSeed : QuerySeed spec) :
--   OracleComp spec (β × QuerySeed spec) := do
--     let missingCount := adv.queryBound - (λ i ↦ (initSeed i).length)
--     let freshSeed : QuerySeed spec ← generateSeed missingCount adv.activeOracles
--     let fullSeed := λ i ↦ initSeed i ++ freshSeed i
--     let z ← simulate' seededOracle fullSeed <| adv.run x
--     return (z, fullSeed)

-- end ForkAdv

namespace OracleComp

-- variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [∀ j, SelectableType (spec.range j)]
--   [unifSpec ⊂ₒ spec] {α β : Type} {i : ι}

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α β γ : Type}

instance {ι : Type} (spec : OracleSpec ι) [unifSpec ⊂ₒ spec] (α : Type) :
    Coe (ProbComp α) (OracleComp spec α) where
  coe := λ oa ↦ SubSpec.liftComp oa

variable [∀ i, SelectableType (spec.range i)]

def fork [unifSpec ⊂ₒ spec] (oa : OracleComp spec α) (qb : ι → ℕ)
    (activeOracles : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (Option (α × α × Fin (qb i + 1))) := do
  let s : Fin (qb i + 1) ← $[0..qb i]
  let sharedSeed : QuerySeed spec ← generateSeed spec (Function.update qb i s) activeOracles
  let seed₁ ← sharedSeed.addValue i <$> ($ᵗ spec.range i)
  let seed₂ ← sharedSeed.addValue i <$> ($ᵗ spec.range i)
  let y₁ ← simulate' seededOracle seed₁ oa
  let y₂ ← simulate' seededOracle seed₂ oa
  return if cf y₁ = some s ∧ cf y₂ = some s ∧ (seed₁ i).getI s ≠ (seed₂ i).getI s
    then some (y₁, y₂, s) else none

variable [unifSpec ⊂ₒ spec] (oa : OracleComp spec α) (qb : ι → ℕ)
    (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))

/-- Proof of non-negligible lower bound on the failure chance of forking a computation
succeeding in producing a result. By the filtering in the final `ite` this bounds the
chance of getting a result with the desired forking semantics. -/
theorem le_probEvent_isSome_fork :
    let frk := [λ z ↦ z.isSome | fork oa qb js i cf]
    let acc := [λ z ↦ z.isSome | cf <$> oa]
    let q : ℝ≥0∞ := qb i
    let h : ℝ≥0∞ := Fintype.card (spec.range i)
    (acc / q) ^ 2 - acc / h ≤ frk := by
  sorry

/-- Theorem expressing the most useful properties of successful forking.
Weaker than the full characterization of the `support` of fork,
but often more useful in practice -/
theorem exists_log_of_mem_support_fork (x₁ x₂ : α) (s : Fin (qb i + 1))
    (h : some (x₁, x₂, s) ∈ ((fork oa qb js i cf)).support) :
    ∃ log₁ : QuerySeed spec, ∃ log₂ : QuerySeed spec,
      (log₁ i).getI s ≠ (log₂ i).getI s ∧
      cf x₁ = some s ∧ cf x₂ = some s ∧
      x₁ ∈ (simulate' loggingOracle ∅ oa).support ∧
      x₂ ∈ (simulate' loggingOracle ∅ oa).support :=
  sorry

end OracleComp
