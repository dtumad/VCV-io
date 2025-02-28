/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append

/-!
# Coercing Oracle Outputs

This file defines a function `liftSO` for lifting a simulation oracle
given a lift from the original to final output oracle sets.

TODO: test if generalized append solves all the problems this was meant to...
-/

-- open OracleSpec OracleComp

-- universe u v w

-- variable {ι ι₁ ι₂ : Type}
--   {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁}
--   {spec₂ : OracleSpec ι₂} {σ α β γ : Type u}

-- namespace SimOracle

-- /-- Given a lifting from oracles in `spec₁` to `spec₂`,
-- and a `SimOracle` from `spec` to `spec₁`, get a simulation from `spec` to `spec₂`
-- by lifting the result of simulation.
-- Actually using a lifted oracle in simulation reduces to the lifting the result
-- of simulating with the base oracle, see `simulateT_liftSO_eq_liftM_simulateT`. -/
-- @[reducible]
-- def liftSO [MonadLift (OracleQuery spec₁) (OracleQuery spec₂)]
--     (so : SimOracle spec spec₁ σ) : SimOracle spec spec₂ σ where
--   impl q := liftM (so.impl q)

-- /-- Automatically lift a simulation oracle given a lift on the output oracle sets.
-- `simp` reduces this back down to `liftSO`. -/
-- instance [MonadLift (OracleQuery spec₁) (OracleQuery spec₂)] :
--     Coe (SimOracle spec spec₁ σ) (SimOracle spec spec₂ σ) where
--   coe := liftSO

-- variable [MonadLift (OracleQuery spec₁) (OracleQuery spec₂)]

-- @[simp]
-- lemma coe_eq_liftSO
--     (so : SimOracle spec spec₁ σ) : (↑so : SimOracle spec spec₂ σ) = so.liftSO := rfl

-- @[simp]
-- lemma impl_liftSO (q : OracleQuery spec α) (so : SimOracle spec spec₁ σ) :
--     (liftSO so : SimOracle spec spec₂ σ).impl q = liftM (so.impl q) := rfl

-- /-- Simulating with lifted simulation oracle is the same as lifting the result of simulation. -/
-- @[simp]
-- lemma simulateT_liftSO_eq_liftM_simulateT
--     (so : SimOracle spec spec₁ σ) (oa : OracleComp spec α) :
--     (simulateT (liftSO so : SimOracle spec spec₂ σ) oa) =
--       liftM (simulateT so oa) := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | query_bind i t oa h =>
--       simp only [StateT.liftM_of_liftM_eq, liftM_eq_liftComp] at h
--       refine StateT.ext fun x => ?_
--       simp [Function.comp_def, h]
--   | failure => simp; rfl

-- example {ι₁ ι₁' ι₂ ι₂' σ τ : Type}
--     {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
--     {specₜ₁ : OracleSpec ι₁'} {specₜ₂ : OracleSpec ι₂'}
--     (so : SimOracle spec₁ specₜ₁ σ) (so' : SimOracle spec₂ specₜ₂ τ) :
--     SimOracle (spec₁ ++ₒ spec₂) (specₜ₁ ++ₒ specₜ₂) (σ × τ) :=
--   liftSO so ++ₛₒ liftSO so'

-- end SimOracle
