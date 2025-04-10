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

structure forkInput (spec : OracleSpec ι) (α : Type) where
  /-- The main program to fork execution of -/
  main : OracleComp spec α
  /-- A bound on the number of queries the adversary makes-/
  queryBound : ι → ℕ
  /-- Specifies the index of which oracle should be forked. -/
  i : ι
  /-- List of oracles that are queried during computation (used to order seed generation). -/
  activeOracles : List ι
  /-- Function that picks out an index of where to do the forking. -/
  chooseFork : α → QueryLog spec → Option (Fin (queryBound i + 1))

/-- Version of `fork` that doesn't choose `s` ahead of time.
Should give better concrete bounds. -/
def fork' (main : OracleComp spec α) (qb : ι → ℕ)
    (js : List ι) (i : ι) (cf : α → Option (Fin (qb i + 1))) :
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

theorem probFailure_fork_le' (main : OracleComp spec α) (qb : ι → ℕ)
    (js : List ι) (i : ι) (cf : α → Option (Fin (qb i + 1))) [spec.FiniteRange] :
    let acc : ℝ≥0∞ := [= none | cf <$> main]
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.range i))
    let k := qb i + 1
    [⊥ | fork' main qb js i cf] ≤ acc * (1 / h + acc / k) := by
  let acc : ℝ≥0∞ := [= none | cf <$> main]
  let h : ℝ≥0∞ := ↑(Fintype.card (spec.range i))
  let k := qb i + 1
  calc [⊥ | fork' main qb js i cf]
  _ = ([⊥ | do
    let seed ← liftM (generateSeed spec qb js)
    let x₁ ← (simulateQ seededOracle main).run seed
    let s : Fin (qb i + 1) ← (cf x₁).getM
    let u ←$ᵗ spec.range i
    guard ((seed i)[s + 1]? ≠ some u)
    let seed' := (seed.takeAtIndex i s).addValue i u
    let x₂ ← (simulateQ seededOracle main).run seed'
    guard (cf x₂ = some s)]) := by
      -- repeat refine probFailure_bind_congr' _ fun _ => ?_
      refine probFailure_bind_congr' _ fun _ =>
        probFailure_bind_congr' _ fun _ =>
        probFailure_bind_congr' _ fun _ =>
        probFailure_bind_congr' _ fun _ =>
        probFailure_bind_congr' _ fun _ =>
        probFailure_bind_congr' _ fun _ => ?_
      simp only [guard_eq, bind_pure_comp, probFailure_map, probFailure_ite,
        probFailure_pure, probFailure_failure]

  -- Sum over possible `s = cf x` values to share
  _ = [= none | cf <$> main] + ∑ s : Fin k, ([⊥ | do
    let seed ← liftM (generateSeed spec qb js)
    let x₁ ← (simulateQ seededOracle main).run seed
    guard (cf x₁ = some s)
    let u ←$ᵗ spec.range i
    guard ((seed i)[s + 1]? ≠ some u)
    let seed' := (seed.takeAtIndex i s).addValue i u
    let x₂ ← (simulateQ seededOracle main).run seed'
    guard (cf x₂ = some s)]) := by
      sorry

  -- Generate only the shared portion of the seed
  _ = [= none | cf <$> main] + ∑ s : Fin k, ([⊥ | do
    let seed ← liftM (generateSeed spec (Function.update qb i s) js)
    let x₁ ← (simulateQ seededOracle main).run seed
    guard (cf x₁ = some s)
    let u ←$ᵗ spec.range i
    guard (some (←$ᵗ spec.range i) ≠ some u)
    let seed' := seed.addValue i u
    let x₂ ← (simulateQ seededOracle main).run seed'
    guard (cf x₂ = some s)]) := by
      sorry

  -- Don't add the extra value `u`
  _ = [= none | cf <$> main] + ∑ s : Fin k, ([⊥ | do
    let seed ← liftM (generateSeed spec (Function.update qb i s) js)
    let x₁ ← (simulateQ seededOracle main).run seed
    guard (cf x₁ = some s)
    guard ((←$ᵗ spec.range i) ≠ (←$ᵗ spec.range i))
    let x₂ ← (simulateQ seededOracle main).run seed
    guard (cf x₂ = some s)]) := by
      sorry

  -- Pull out the odds of getting a duplicate query output
  _ = [= none | cf <$> main] + ∑ s : Fin k, ([⊥ | do
    let seed ← liftM (generateSeed spec (Function.update qb i s) js)
    let x₁ ← (simulateQ seededOracle main).run seed
    guard (cf x₁ = some s)
    let x₂ ← (simulateQ seededOracle main).run seed
    guard (cf x₂ = some s)] - 1 / h) := by
      sorry

  -- Convert failure to getting specific outputs
  _ = [= none | cf <$> main] + ∑ s : Fin k, ((1 - [= (some s, some s) | do
    let seed ← liftM (generateSeed spec (Function.update qb i s) js)
    let s₁ ← cf <$> (simulateQ seededOracle main).run seed
    let s₂ ← cf <$> (simulateQ seededOracle main).run seed
    return (s₁, s₂)]) - 1 / h) := by
      sorry

  -- Convert failure to getting specific outputs
  _ ≤ [= none | cf <$> main] + ∑ s : Fin k, ((1 - [= some s | do
    let seed ← liftM (generateSeed spec (Function.update qb i s) js)
    let s₁ ← cf <$> (simulateQ seededOracle main).run seed
    return s₁] ^ 2 / k)) - k / h := by
      sorry

  -- Simplify with only one run of the computation
  _ ≤ [= none | cf <$> main] + (∑ s : Fin k, (1 - [= some s | cf <$> main] ^ 2 / k)) - k / h := by
      sorry

  -- _ = [= none | cf <$> main] +

  _ ≤ acc * (1 / h + acc / k) := sorry

  -- rw [fork']
  -- rw [probFailure_bind_of_neverFails]
  -- · simp only
  --   sorry
  -- · simp
  --   sorry

def fork (main : OracleComp spec α) (i : ι) (qb : ι → ℕ)
    (js : List ι) (cf : α → QueryLog spec → Option (Fin (qb i + 1))) :
    OracleComp spec (α × α) := do
  -- let ⟨main, qb, i, activeOracles, cf⟩ := input
  -- Choose a random query index `s` at which to fork the execution
  let s : Fin (qb i + 1) ← $[0..qb i]
  let qb' : ι → ℕ := update qb i s
  -- Generate a shared seed for the initial execution
  let sharedSeed : QuerySeed spec ← generateSeed spec qb' js
  -- Generate the query outputs for the query to be forked
  let u₁ ←$ᵗ spec.range i
  let u₂ ←$ᵗ spec.range i
  guard (u₁ ≠ u₂)
  let seed₁ := sharedSeed.addValue i u₁
  let seed₂ := sharedSeed.addValue i u₂
  -- Execute the program with the two slightly different seeds
  let (x₁, log₁) ← (simulateQ seededOracle.withLogging main).run.run seed₁
  let (x₂, log₂) ← (simulateQ seededOracle.withLogging main).run.run seed₂
  -- Check that `cf` chooses to fork at `s` in both cases
  guard (cf x₁ log₁ = some s ∧ cf x₂ log₂ = some s)
  return (x₁, x₂)

/-- Call fork using the fields of a `forkInput` structure. -/
def fork_input (input : forkInput spec α) : OracleComp spec (α × α) :=
  fork input.main input.i input.queryBound input.activeOracles input.chooseFork

variable [unifSpec ⊂ₒ spec] (main : OracleComp spec α) (i : ι) (qb : ι → ℕ)
    (js : List ι) (cf : α → QueryLog spec → Option (Fin (qb i + 1)))

/-- Proof of non-negligible lower bound on the failure chance of forking a computation
succeeding in producing a result. By the filtering in the final `ite` this bounds the
chance of getting a result with the desired forking semantics. -/
theorem probFailure_fork_le [spec.FiniteRange] :
    let acc := [λ (x, log) ↦ (cf x log).isSome | (simulateQ loggingOracle main).run]
    let q : ℝ≥0∞ := qb i
    let h : ℝ≥0∞ := Fintype.card (spec.range i)
    [⊥ | fork main i qb js cf] ≤ 1 / h + (acc / q) ^ 2 := by
  sorry -- TODO: proof after change to "guard"

-- /-- Succesfull outputs of `fork oa qb js i cf` are outputs of running `oa` with a seeded oracle
-- where the seeds agree up until query `s` to the oracle at index `i`, at which point
-- they give distinct outputs to the query. Additionally the `cf` function chooses `s`
-- as the index on both of the outputs. -/
-- lemma some_mem_support_fork_iff (x₁ x₂ : α) (s : Fin (qb i + 1)) :
--     some (x₁, x₂, s) ∈ (fork oa qb js i cf).support ↔
--       cf x₁ = some s ∧ cf x₂ = some s ∧
--       ∃ shared_seed ∈ (generateSeed spec (update qb i s) js).support,
--         ∃ u₁ u₂ : spec.range i, u₁ ≠ u₂ ∧
--           x₁ ∈ (simulate' seededOracle (shared_seed.addValue i u₁) oa).support ∧
--           x₂ ∈ (simulate' seededOracle (shared_seed.addValue i u₂) oa).support :=
--   sorry

/-- Theorem expressing the most useful properties of successful forking,
framed in terms of `loggingOracle` instead of `seededOracle`.
Weaker than the full characterization of the `support` of fork,
but often more useful in practice -/
theorem exists_log_of_mem_support_fork (x₁ x₂ : α) (s : Fin (qb i + 1))
    (hcf : ∀ x log, (cf x log) = some s → ↑s < log.countQ i)
    (h : (x₁, x₂) ∈ ((fork main i qb js cf)).support) :
    ∃ log₁ : QueryLog spec, ∃ log₂ : QueryLog spec,
      ∃ h₁ : cf x₁ log₁ = some s, ∃ h₂ : cf x₂ log₂ = some s,
      let hcf₁ : ↑s < log₁.countQ i := hcf x₁ log₁ h₁
      let hcf₂ : ↑s < log₂.countQ i := hcf x₂ log₂ h₂
      (log₁.getQ i)[s].1 = (log₂.getQ i)[s].1 ∧
      (log₁.getQ i)[s].2 ≠ (log₂.getQ i)[s].2 ∧
      (x₁, log₁) ∈ (simulateQ loggingOracle main).run.support ∧
      (x₂, log₂) ∈ (simulateQ loggingOracle main).run.support := sorry -- TODO: proof after guard ch

end OracleComp
