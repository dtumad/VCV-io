/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio

/-!
# Random-Function Random-Permutation Switching Lemma
-/

open OracleSpec OracleComp ENNReal

-- /-- Security adversary for RF-RP distinguisher experiments. -/
-- def RF_RP_Adv' (α : ℕ → Type) [∀ n, Fintype (α n)]
--     [∀ n, Inhabited (α n)] [∀ n, DecidableEq (α n)] :=
--   SecAdv (λ n ↦ (α n →ₒ α n)) (λ _ ↦ Unit) (λ _ ↦ Bool)

/-- Security adversary for RF-RP distinguisher experiments.
Note: We don't give the adversary a `unifSpec` oracle, it only has distinguisher pieces. -/
def RF_RP_Adv (α : ℕ → Type) [∀ n, Fintype (α n)]
    [∀ n, Inhabited (α n)] [∀ n, DecidableEq (α n)] :=
  SecAdv (λ n ↦ (α n →ₒ α n)) (λ _ ↦ Unit) (λ _ ↦ Bool)

variable {α : ℕ → Type} [∀ n, Fintype (α n)]
    [∀ n, Inhabited (α n)] [∀ n, DecidableEq (α n)]
    [∀ n, SelectableType (α n)]

/-- Run a `RF_RP_Adv` using a random function to answer queries,
implemented as a simulation with a random oracle. -/
def RF_Exp (adv : RF_RP_Adv α) :
    SecExp (λ n ↦ (α n →ₒ α n)) where
  main n := (· = true) <$> adv.run n ()
  baseState n := QueryCache (α n →ₒ α n)
  init_state _ := ∅
  baseSimOracle _ := randOracle

/-- Run a `RF_RP_Adv` using a random permutation to answer queries.
The simulation uses an additional finset to avoid choosing duplicate query outputs.

Note: We could implement a `randUniqOracle` rather than do this ad hoc. unsure other use cases. -/
noncomputable def RP_Exp (adv : RF_RP_Adv α) :
    SecExp (λ n ↦ (α n →ₒ α n)) where
  main n := (· = false) <$> adv.run n ()
  baseState n := QueryCache (α n →ₒ α n) × Finset (α n)
  init_state _ := (∅, ∅)
  baseSimOracle _ := λ () t (cache, used) ↦ do
    let (u, cache') ← cache.lookup_or_else () t ($ usedᶜ)
    return (u, cache', insert u used)

noncomputable def RF_RP_distinguisher_advantage (adv : RF_RP_Adv α) (n : ℕ) : ℝ≥0∞ :=
  (RF_Exp adv).advantage n + (RP_Exp adv).advantage n

theorem RF_RP_switching_lemma (adv : RF_RP_Adv α) (n : ℕ) :
    let q : ℕ := (adv.qb ()).eval n
    let k : ℕ := Fintype.card (α n)
    (RF_RP_distinguisher_advantage adv) ≤ 1 + q * (q + 1) / k ^ n :=
  sorry
