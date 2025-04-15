/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.GenerateSeed
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.Coercions.Append

/-!
# Forking Lemma

-/

open OracleSpec OracleComp Option ENNReal Function

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [∀ i, SelectableType (spec.range i)] [spec.DecidableEq] [unifSpec ⊂ₒ spec]
  {α β γ : Type}

section scratch

lemma probFailure_bind_congr [spec.FiniteRange] (oa : OracleComp spec α)
    {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ}
    (h : ∀ x ∈ oa.support, [⊥ | ob x] = [⊥ | oc x]) : [⊥ | oa >>= ob] = [⊥ | oa >>= oc] := by
  sorry

lemma probFailure_bind_congr' [spec.FiniteRange] (oa : OracleComp spec α)
    {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ}
    (h : ∀ x, [⊥ | ob x] = [⊥ | oc x]) : [⊥ | oa >>= ob] = [⊥ | oa >>= oc] := by
  sorry

lemma probFailure_bind_eq_sum_probFailure [spec.FiniteRange] (oa : OracleComp spec α)
    {ob : α → OracleComp spec β} {σ : Type _} {s : Finset σ}
    {oc : σ → α → OracleComp spec γ}
    :
    [⊥ | oa >>= ob] = ∑ x ∈ s, [⊥ | oa >>= oc x] :=
    sorry

end scratch

structure forkInput (spec : OracleSpec ι) (α : Type) where
  /-- The main program to fork execution of -/
  main : OracleComp spec α
  /-- A bound on the number of queries the adversary makes-/
  queryBound : ι → ℕ
  /-- List of oracles that are queried during computation (used to order seed generation). -/
  js : List ι

/-- Version of `fork` that doesn't choose `s` ahead of time.
Should give better concrete bounds. -/
def fork' (main : OracleComp spec α)
    (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (α × α) := do
  let seed ← generateSeed spec qb js
  let x₁ ← (simulateQ seededOracle main).run seed
  let s : Fin (qb i + 1) ← (cf x₁).getM
  let u ←$ᵗ spec.range i -- Choose new output for query
  guard ((seed i)[s + 1]? ≠ some u) -- Didn't pick the same output
  let seed' := (seed.takeAtIndex i s).addValue i u
  let x₂ ← (simulateQ seededOracle main).run seed'
  guard (cf x₂ = some s) -- Choose the same index on this run
  return (x₁, x₂)

variable (main : OracleComp spec α) (qb : ι → ℕ)
    (js : List ι) (i : ι) (cf : α → Option (Fin (qb i + 1))) [spec.FiniteRange]

lemma le_probOutput_fork (s : Fin (qb i + 1)) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.range i))
    let q := qb i + 1
    [= s | cf <$> main] ^ 2 - [= s | cf <$> main] / h
      ≤ [fun (x₁, x₂) => cf x₁ = s ∧ cf x₂ = s | fork' main qb js i cf] :=
  let h : ℝ≥0∞ := ↑(Fintype.card (spec.range i))
  let q := qb i + 1
  calc [fun (x₁, x₂) => cf x₁ = some s ∧ cf x₂ = some s | fork' main qb js i cf]
    _ = [= (some s, some s) | Prod.map cf cf <$> fork' main qb js i cf] := sorry
    -- Open the forking definition up
    _ = [= (some s, some s) | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          let u ←$ᵗ spec.range i
          guard ((seed i)[s + 1]? ≠ some u)
          let seed' := (seed.takeAtIndex i s).addValue i u
          let x₂ ← (simulateQ seededOracle main).run seed'
          return (cf x₁, cf x₂)] := sorry
    -- Split on whether the middle `guard` will fail
    _ ≥ [= (some s, some s) | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          let u ←$ᵗ spec.range i
          let seed' := (seed.takeAtIndex i s).addValue i u
          let x₂ ← (simulateQ seededOracle main).run seed'
          return (cf x₁, cf x₂)] -
        [= some s | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          let u ←$ᵗ spec.range i
          guard ((seed i)[s + 1]? = some u)
          return (cf x₁)] := sorry
    -- Simplify both of the expressions
    _ = [= (some s, some s) | do
          let shared_seed ← liftM (generateSeed spec (Function.update qb i q) js)
          let x₁ ← (simulateQ seededOracle main).run shared_seed
          let x₂ ← (simulateQ seededOracle main).run shared_seed
          return (cf x₁, cf x₂)] -
        [= some s | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          return (cf x₁)] / h := sorry
    _ ≥ [= some s | cf <$> main] ^ 2 - [= some s | cf <$> main] / h := sorry

theorem probFailure_fork_le :
    let acc : ℝ≥0∞ := 1 - [= none | cf <$> main]
    let h : ℝ≥0∞ := Fintype.card (spec.range i)
    let q := qb i + 1
    [⊥ | fork' main qb js i cf] ≤ 1 - acc * (acc / q - h⁻¹) := by
  let acc : ℝ≥0∞ := 1 - [= none | cf <$> main]
  let h : ℝ≥0∞ := Fintype.card (spec.range i)
  let q := qb i + 1
  calc [⊥ | fork' main qb js i cf]
    _ = 1 - ∑ s, [= (s, s) | Prod.map cf cf <$> fork' main qb js i cf] := by
      sorry
    _ ≤ 1 - ∑ s, ([= s | cf <$> main] ^ 2 - [= s | cf <$> main] / h) := by
      sorry
    _ = 1 - (∑ s, [= s | cf <$> main] ^ 2) - (∑ s, [= s | cf <$> main] / h) := by
      sorry
    _ ≤ 1 - (∑ s, [= s | cf <$> main]) ^ 2 / q - (∑ s, [= s | cf <$> main]) / h := by
      sorry
    _ ≤ 1 - acc ^ 2 / q + acc / h := by
      sorry
    _ = 1 - acc * (acc / q - h⁻¹) := by
      sorry

theorem exists_log_of_mem_support_fork (x₁ x₂ : α)
    (h : (x₁, x₂) ∈ (fork' main qb js i cf).support) :
      ∃ s, cf x₁ = some s ∧ cf x₂ = some s ∧
      ∃ log₁ : QueryLog spec, ∃ hcf₁ : ↑s < log₁.countQ i,
      ∃ log₂ : QueryLog spec, ∃ hcf₁ : ↑s < log₂.countQ i,
      (log₁.getQ i)[s].1 = (log₂.getQ i)[s].1 ∧
      (log₁.getQ i)[s].2 ≠ (log₂.getQ i)[s].2 ∧
      (x₁, log₁) ∈ (simulateQ loggingOracle main).run.support ∧
      (x₂, log₂) ∈ (simulateQ loggingOracle main).run.support :=
  sorry

end OracleComp
