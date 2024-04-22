/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.GenerateSeed
import VCVio.OracleComp.OracleSpec.SubSpec

/-!
# Forking Lemma

-/

open OracleSpec OracleComp OracleAlg Option ENNReal

structure ForkAdv (spec : OracleSpec)
    (α β : Type) (i : spec.ι)
    extends SecAdv spec α β where
  chooseFork : α → β →
    Option (Fin (queryBound i + 1))

namespace ForkAdv

variable {spec : OracleSpec} [∀ j, SelectableType (spec.range j)]
  [unifSpec ⊂ₒ spec]

def seedAndRun (adv : ForkAdv spec α β i)
    (x : α) (initSeed : QuerySeed spec) :
  OracleComp spec (β × QuerySeed spec) := do
    let missingCount := adv.queryBound - (λ i ↦ (initSeed i).length)
    let freshSeed : QuerySeed spec ← generateSeed missingCount adv.activeOracles
    let fullSeed := λ i ↦ initSeed i ++ freshSeed i
    let z ← simulate' seededOracle fullSeed <| adv.run x
    return (z, fullSeed)

end ForkAdv

namespace OracleComp

variable {spec : OracleSpec} [∀ j, SelectableType (spec.range j)]
  [unifSpec ⊂ₒ spec]

def fork (adv : ForkAdv spec α β i) :
    SecAdv spec α (Option (β × β)) where
  run := λ x ↦ do
    -- pre-select where to fork execution
    let s : Fin _ ← $[0..adv.queryBound i]
    let qc := Function.update adv.queryBound i s
    -- Generate shared seed for both runs
    let sharedSeed ← generateSeed qc adv.activeOracles
    let ⟨y₁, seed₁⟩ ← adv.seedAndRun x sharedSeed
    let ⟨y₂, seed₂⟩ ← adv.seedAndRun x sharedSeed
    -- Only return a value on success
    if adv.chooseFork x y₁ = some s ∧
        adv.chooseFork x y₂ = some s ∧
        (seed₁ i).getI s ≠ (seed₂ i).getI s
      then return some (y₁, y₂)
      else return none
  queryBound := 2 • adv.queryBound
  activeOracles := adv.activeOracles

theorem le_fork_advantage
    (adv : ForkAdv spec α β i) (x : α) :
    let frk := [(· ≠ none) | (fork adv).run x]
    let acc := [(· ≠ none) | adv.chooseFork x <$> adv.run x]
    let q : ℝ≥0∞ := adv.queryBound i + 1
    let h : ℝ≥0∞ := Fintype.card (spec.range i)
    (acc / q) ^ 2 - acc / h ≤ frk :=
  sorry

end OracleComp
