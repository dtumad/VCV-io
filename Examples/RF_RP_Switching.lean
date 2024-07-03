/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio

/-!
# Random Function/Permutation Switching Lemma


-/

open OracleSpec OracleComp ENNReal

-- variable {ι : Type} {spec : OracleSpec ι}

structure RF_RP_Distinguisher (α : Type) [Inhabited α]
    [DecidableEq α] [Fintype α] where
  run : OracleComp (α →ₒ α) Bool

-- def RF_RP_Distinguisher' (α : Type) [Inhabited α]
--     [DecidableEq α] [Fintype α] :=
--   SecAdv (λ _ ↦ (α →ₒ α)) (λ _ ↦ Unit) (λ _ ↦ Bool)


instance (α : Type) [Inhabited α] : Inhabited {f : α → α // f.Bijective} :=
    sorry

variable {α : Type} [Inhabited α] [DecidableEq α] [Fintype α]
  [SelectableType (α → α)] [SelectableType {f : α → α // f.Bijective}]

namespace RF_RP_Distinguisher

-- def RF_distinguishExp (adv : RF_RP_Distinguisher α) :
--     OracleComp unifSpec Bool := do
--   let f ←$ᵗ (α → α)
--   simulate' (λ () t () ↦ return (f t, ())) () adv.run

-- def RP_distinguishExp (adv : RF_RP_Distinguisher α) :
--     OracleComp unifSpec Bool := do
--   let f ←$ᵗ

def RF_RP_distinguishExp (adv : RF_RP_Distinguisher α) :
    OracleComp unifSpec Bool := do
  let b : Bool ← coin
  let f ←$ᵗ (α → α)
  let g ←$ᵗ ({f : α → α // f.Bijective})
  let fg := if b then f else g.1
  let b' ← simulate' (λ () t () ↦ return (fg t, ())) () adv.run
  return b = b'

-- def advantage (adv : RF_RP_Distinguisher α) : ℝ≥0∞ := 0


end RF_RP_Distinguisher

-- def RF_RP_distinguishExp (adv : RF_RP_Distinguisher α) :
--     SecExp (λ _ ↦ unifSpec) where
--   main := λ
--   __ := OracleAlg.baseOracleAlg
