/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
-- import VCVio.OracleComp.Constructions.GenerateSeed
-- import VCVio.OracleComp.OracleSpec.SubSpec

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

-- -- def fork (adv : ForkAdv spec α β i) :
-- --     SecAdv spec α (Option (β × β)) where
-- --   run := λ x ↦ do
-- --     -- pre-select where to fork execution
-- --     let s : Fin _ ← $[0..adv.queryBound i]
-- --     let qc := Function.update adv.queryBound i s
-- --     -- Generate shared seed for both runs
-- --     let sharedSeed : QuerySeed spec ← ↑(generateSeed qc adv.activeOracles)
-- --     -- Add the forked queries to the two seeds
-- --     let seed₁ ← sharedSeed.addValue i <$> ($ᵗ spec.range i)
-- --     let seed₂ ← sharedSeed.addValue i <$> ($ᵗ spec.range i)
-- --     -- Run the adversary on both seeds
-- --     let y₁ ← simulate' seededOracle seed₁ (adv.run x)
-- --     let y₂ ← simulate' seededOracle seed₂ (adv.run x)
-- --     -- Only return a value on success
-- --     if adv.chooseFork x y₁ = some s ∧
-- --         adv.chooseFork x y₂ = some s ∧
-- --         (seed₁ i).getI s ≠ (seed₂ i).getI s
-- --       then return some (y₁, y₂)
-- --       else return none
-- --   queryBound := 2 • adv.queryBound
-- --   activeOracles := adv.activeOracles

-- theorem some_mem_support_fork_iff (adv : ForkAdv spec α β i) (x : α) (y₁ y₂ : β)
--     (h : some (y₁, y₂) ∈ ((fork adv).run x).support) :
--     ∃ s : Fin (adv.queryBound i + 1), ∃ seed₁ seed₂ : QuerySeed spec,
--       ∃ h₁ : ↑s < (seed₁ i).length, ∃ h₂ : ↑s < (seed₂ i).length,
--         (seed₁ i)[↑s]'h₁ ≠ (seed₂ i)[↑s]'h₂ ∧
--         y₁ ∈ (simulate' seededOracle seed₁ (adv.run x)).support ∧
--         y₂ ∈ (simulate' seededOracle seed₂ (adv.run x)).support ∧
--         adv.chooseFork x y₁ = some s ∧ adv.chooseFork x y₂ = some s :=
--   alignPort

-- theorem le_fork_advantage
--     (adv : ForkAdv spec α β i) (x : α) :
--     let frk := [(· ≠ none) | (fork adv).run x]
--     let acc := [(· ≠ none) | adv.chooseFork x <$> adv.run x]
--     let q : ℝ≥0∞ := adv.queryBound i + 1
--     let h : ℝ≥0∞ := Fintype.card (spec.range i)
--     (acc / q) ^ 2 - acc / h ≤ frk :=
--   alignPort

end OracleComp
