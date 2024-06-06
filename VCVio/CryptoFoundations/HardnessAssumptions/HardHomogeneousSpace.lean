/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
-- import VCVio.OracleComp.Constructions.UniformSelect

/-!
# Hard Homogeneous Spaces

This file builds up the definition of a hard homogeneous space, an extension of a group action
on some set such that the action of each group element defines a bijection.
We use mathlib's `AddTorsor` type class to represent the bijection property,
and extend this with finiteness and decidability conditions
-/

open OracleSpec OracleComp OracleAlg BigOperators ENNReal

section testing


class HomogeneousSpace' (G : semiOutParam (ℕ → Type))
    (P : semiOutParam (ℕ → Type)) :=
  AddGroup_G (sp : ℕ) : AddGroup (G sp)
  AddTorsor_GP (sp : ℕ) : AddTorsor (G sp) (P sp)
  decidableEq_G (sp : ℕ) : DecidableEq (G sp)
  decidableEq_P (sp : ℕ) : DecidableEq (P sp)
  fintype_G (sp : ℕ) : Fintype (G sp)
  fintype_P (sp : ℕ) : Fintype (P sp)
  inhabited_G (sp : ℕ) : Inhabited (G sp)
  inhabited_P (sp : ℕ) : Inhabited (P sp)
  selectableType_G (sp : ℕ) : SelectableType (G sp)
  selectableType_P (sp : ℕ) : SelectableType (P sp)

variable (G P : ℕ → Type)

instance [h : HomogeneousSpace' G P] (sp : ℕ) : AddGroup (G sp) := h.AddGroup_G sp
instance [h : HomogeneousSpace' G P] (sp : ℕ) : AddTorsor (G sp) (P sp) := h.AddTorsor_GP sp
instance [h : HomogeneousSpace' G P] (sp : ℕ) : DecidableEq (G sp) := h.decidableEq_G sp
instance [h : HomogeneousSpace' G P] (sp : ℕ) : DecidableEq (P sp) := h.decidableEq_P sp
instance [h : HomogeneousSpace' G P] (sp : ℕ) : Fintype (G sp) := h.fintype_G sp
instance [h : HomogeneousSpace' G P] (sp : ℕ) : Fintype (P sp) := h.fintype_P sp
instance [h : HomogeneousSpace' G P] (sp : ℕ) : Inhabited (G sp) := h.inhabited_G sp
instance [h : HomogeneousSpace' G P] (sp : ℕ) : Inhabited (P sp) := h.inhabited_P sp
instance [h : HomogeneousSpace' G P] (sp : ℕ) : SelectableType (G sp) := h.selectableType_G sp
instance [h : HomogeneousSpace' G P] (sp : ℕ) : SelectableType (P sp) := h.selectableType_P sp

structure SecAdv' {ι : Type}
    (spec : ℕ → OracleSpec ι)
    (α β : ℕ → Type) where
  run (sp : ℕ) : α sp → OracleComp (spec sp) (β sp)

structure OracleAlg' {ι : Type} (spec : ℕ → OracleSpec ι) where
  baseState (sp : ℕ) : Type
  init_state (sp : ℕ) : baseState sp
  baseSimOracle (sp : ℕ) : spec sp →[baseState sp]ₛₒ unifSpec

@[inline, reducible]
def baseOracleAlg' : OracleAlg' (λ _ ↦ unifSpec) where
  baseState := λ _ ↦ Unit
  init_state := λ _ ↦ ()
  baseSimOracle := λ _ ↦ idOracle

structure SecExp' {ι : Type} (spec : ℕ → OracleSpec ι)
    (α : ℕ → Type)
    extends OracleAlg' spec where
  inpGen (sp : ℕ) : OracleComp (spec sp) (α sp)
  main (sp : ℕ) : α sp → OracleComp (spec sp) Bool

structure SecExp'' {ι : Type} (spec : ℕ → OracleSpec ι)
    -- (α : ℕ → Type)
    extends OracleAlg' spec where
  -- inpGen (sp : ℕ) : OracleComp (spec sp) (α sp)
  main (sp : ℕ) : OracleComp (spec sp) Bool

def VectorizationAdv' (G P : (sp : ℕ) → Type) :=
  SecAdv' (λ _ ↦ unifSpec) (λ sp ↦ P sp × P sp) (λ sp ↦ G sp)

def vectorizationExp'' (G P : ℕ → Type)
    [HomogeneousSpace' G P]
    (adv : VectorizationAdv' G P) :
    SecExp' (λ _ ↦ unifSpec)
      (λ sp ↦ P sp × P sp) where
  inpGen := λ sp ↦ (·, ·) <$> ($ᵗ P sp) <*> ($ᵗ P sp)
  main := λ sp (x₁, x₂) ↦ do
    let g ← adv.run sp (x₁, x₂)
    return g = x₁ -ᵥ x₂
  __ := baseOracleAlg'

def vectorizationExp''' (G P : ℕ → Type)
    [HomogeneousSpace' G P]
    (adv : VectorizationAdv' G P) :
    SecExp'' (λ _ ↦ unifSpec) where
  main := λ sp ↦ do
    let x₁ ← $ᵗ P sp
    let x₂ ← $ᵗ P sp
    let g ← adv.run sp (x₁, x₂)
    return g = x₁ -ᵥ x₂
  __ := baseOracleAlg'

def vectorizationExp' (G P : ℕ → Type)
    [HomogeneousSpace' G P]
    (adv : VectorizationAdv' G P) (sp : ℕ) :
    OracleComp unifSpec Bool := do
      let x₁ ← $ᵗ (P sp)
      let x₂ ← $ᵗ (P sp)
      let g ← adv.run sp (x₁, x₂)
      return g = x₁ -ᵥ x₂

noncomputable def vectorizationAdvantage' (G P : ℕ → Type)
    [HomogeneousSpace' G P]
    (adv : VectorizationAdv' G P) (sp : ℕ) : ℝ≥0∞ :=
    [= true | vectorizationExp' G P adv sp]

-- TODO: fix
def negligible (f : ℕ → ℝ≥0∞) : Prop := f ≠ λ _ ↦ ∞

def vectorizationHard' (G P : ℕ → Type)
    [HomogeneousSpace' G P] : Prop :=
  ∀ adv, negligible (λ sp ↦ vectorizationAdvantage' G P adv sp)

end testing

/-- A `HomogeneousSpace G P` is a group action of a group `G` on a set of points `P`,
such that the action induces a bijection (represented by the `AddTorsor` class),
with the additional assumption that both spaces are finite. -/
class HomogeneousSpace (G : outParam Type) (P : semiOutParam Type)
    [outParam (AddGroup G)]
    extends AddTorsor G P where
  decidableEq_G : DecidableEq G
  decidableEq_P : DecidableEq P
  fintype_G : Fintype G
  fintype_P : Fintype P
  inhabited_G : Inhabited G
  inhabited_P : Inhabited P
  selectableType_G : SelectableType G
  selectableType_P : SelectableType P

namespace HomogeneousSpace

variable {G P : Type} [AddGroup G]

instance [h : HomogeneousSpace G P] : DecidableEq G := h.decidableEq_G
instance [h : HomogeneousSpace G P] : DecidableEq P := h.decidableEq_P
instance [h : HomogeneousSpace G P] : Fintype G := h.fintype_G
instance [h : HomogeneousSpace G P] : Fintype P := h.fintype_P
instance [h : HomogeneousSpace G P] : Inhabited G := h.inhabited_G
instance [h : HomogeneousSpace G P] : Inhabited P := h.inhabited_P
instance [h : HomogeneousSpace G P] : SelectableType G := h.selectableType_G
instance [h : HomogeneousSpace G P] : SelectableType P := h.selectableType_P

/-- An adversary for the vectorization game takes in a pair of base points `(x₁, x₂)`,
and attempts to generate a vectorization, i.g. a vector `g` with `g +ᵥ x₂ = x₁`.

TODO: how does ":=" compare to "extends" in practice? -/
structure vectorizationAdv (G P : Type)
  extends SecAdv unifSpec (P × P) G

/-- Analogue of the game for the discrete logarithm assumption.
The input generator randomly chooses the challenge points for the adversary,
and a result is valid if it is exactly the vectorization of the challenge points. -/
noncomputable def vectorizationExp [HomogeneousSpace G P]
    (adv : vectorizationAdv G P) : SecExp unifSpec (P × P) where
  inpGen := (·, ·) <$> ($ᵗ P) <*> ($ᵗ P)
  main := λ (x₁, x₂) ↦ do
    let g ← adv.run (x₁, x₂)
    return g = x₁ -ᵥ x₂
  __ := baseOracleAlg

namespace vectorizationExp

@[simp]
lemma advantage_eq [HomogeneousSpace G P] (adv : vectorizationAdv G P) :
    (vectorizationExp adv).advantage =
      ∑ x₁ : P, ∑ x₂ : P, [= x₁ -ᵥ x₂ | adv.run (x₁, x₂)] / (Fintype.card P) ^ 2 := by
  simp [vectorizationExp, Finset.mul_sum]
  sorry

end vectorizationExp

end HomogeneousSpace
