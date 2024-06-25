-- /-
-- Copyright (c) 2024 Devon Tuma. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Devon Tuma
-- -/
-- import VCVio.OracleComp.Coercions.SubSpec

-- /-!
-- # Coercions of Uniform Selection

-- This file defines a typeclass `hasUnifSelect` for oracle sets that contain `unifSpec`.
-- This allows computations like `coin` or `$[0..n]` to be automatically coerced to one with oracles
-- like `spec ++ₒ unifSpec`.

-- TODO: do we still need this?
-- -/

-- namespace OracleSpec

-- -- Note: we need to change to this because of the index set move
-- class hasUnifSelect {ι : Type} (spec : OracleSpec ι) : Type 1 where
--   toFun (n : ℕ) : OracleComp spec (Fin (n + 1))

-- instance {ι : Type} (spec : OracleSpec ι) [h : hasUnifSelect spec] : unifSpec ⊂ₒ spec where
--   toFun := λ n _ ↦ h.toFun n
--   evalDist_toFun' := sorry

-- end OracleSpec

-- namespace OracleComp

-- instance {ι : Type} {spec : OracleSpec ι} [spec.hasUnifSelect] {α : Type} :
--     Coe (OracleComp unifSpec α) (OracleComp spec α) where
--   coe := liftComp

-- end OracleComp
