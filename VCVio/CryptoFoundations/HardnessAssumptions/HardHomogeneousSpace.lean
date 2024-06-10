/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation

/-!
# Hard Homogeneous Spaces

This file builds up the definition of a hard homogeneous space, an extension of a group action
on some set such that the action of each group element defines a bijection.
We use mathlib's `AddTorsor` type class to represent the bijection property,
and extend this with finiteness and decidability conditions
-/

open OracleSpec OracleComp OracleAlg BigOperators ENNReal

class HomogeneousSpace (G : semiOutParam (ℕ → Type))
    (P : semiOutParam (ℕ → Type)) :=
  AddGroup_G (sp : ℕ) : AddCommGroup (G sp)
  AddTorsor_GP (sp : ℕ) : AddTorsor (G sp) (P sp)
  decidableEq_G (sp : ℕ) : DecidableEq (G sp)
  decidableEq_P (sp : ℕ) : DecidableEq (P sp)
  fintype_G (sp : ℕ) : Fintype (G sp)
  fintype_P (sp : ℕ) : Fintype (P sp)
  inhabited_G (sp : ℕ) : Inhabited (G sp)
  inhabited_P (sp : ℕ) : Inhabited (P sp)
  selectableType_G (sp : ℕ) : SelectableType (G sp)
  selectableType_P (sp : ℕ) : SelectableType (P sp)

namespace HomogeneousSpace

variable (G P : ℕ → Type)

instance [h : HomogeneousSpace G P] (sp : ℕ) : AddCommGroup (G sp) := h.AddGroup_G sp
instance [h : HomogeneousSpace G P] (sp : ℕ) : AddTorsor (G sp) (P sp) := h.AddTorsor_GP sp
instance [h : HomogeneousSpace G P] (sp : ℕ) : DecidableEq (G sp) := h.decidableEq_G sp
instance [h : HomogeneousSpace G P] (sp : ℕ) : DecidableEq (P sp) := h.decidableEq_P sp
instance [h : HomogeneousSpace G P] (sp : ℕ) : Fintype (G sp) := h.fintype_G sp
instance [h : HomogeneousSpace G P] (sp : ℕ) : Fintype (P sp) := h.fintype_P sp
instance [h : HomogeneousSpace G P] (sp : ℕ) : Inhabited (G sp) := h.inhabited_G sp
instance [h : HomogeneousSpace G P] (sp : ℕ) : Inhabited (P sp) := h.inhabited_P sp
instance [h : HomogeneousSpace G P] (sp : ℕ) : SelectableType (G sp) := h.selectableType_G sp
instance [h : HomogeneousSpace G P] (sp : ℕ) : SelectableType (P sp) := h.selectableType_P sp

class vectorizationHard (G P : ℕ → Type) [HomogeneousSpace G P]
    extends HardRelation (λ n ↦ P n × P n) (λ n ↦ G n)
      (λ (x₁, x₂) g ↦ g = x₁ -ᵥ x₂)

class parallelizationHard (G P : ℕ → Type) [HomogeneousSpace G P]
    extends HardRelation (λ n ↦ P n × P n × P n) (λ n ↦ P n)
      (λ (x₁, x₂, x₃) x₄ ↦ x₁ -ᵥ x₂ = x₃ -ᵥ x₄)

end HomogeneousSpace
