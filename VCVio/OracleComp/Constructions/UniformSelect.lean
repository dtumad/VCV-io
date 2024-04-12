/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
-- import VCVio.OracleComp.SimSemantics.Constructions
-- import VCVio.OracleComp.OracleSpec.SubSpec
import VCVio.OracleComp.DistSemantics.EvalDist
import Mathlib.Data.Vector.Mem

/-!
# Selecting Uniformly From a Collection

This file defines some computations for selecting uniformly at random from a number
of different collections, using `unifSpec` to make the random choices.
-/

open OracleSpec OracleComp BigOperators ENNReal

namespace OracleComp

section Selectable

/-- `Selectable α β` means that a value of type `β` can be chosen uniformly from
a collection of type `α`. This amounts to being able to choose a canonical vector `elemVec`
from which they will actually be drawn (see `uniformSelect`). -/
class Selectable (α : Type) (β : Type) where
  count : α → ℕ
  elemVec : (s : α) → Vector β (count s + 1)

/-- Given a selectable object, we can get a random element by indexing into the element vector. -/
def uniformSelect {α : Type} {β : Type} [h : Selectable α β] (s : α) :
    OracleComp unifSpec β := do
  let i ← $[0..h.count s]
  return (h.elemVec s).get i

notation "$" => uniformSelect

variable {α : Type} {β : Type}

@[simp]
lemma evalDist_uniformSelect [h : Selectable α β] (s : α) :
    evalDist ($ s) = PMF.ofMultiset (Multiset.ofList (h.elemVec s).toList)
      (by simp [← List.length_eq_zero]) := by
  simp [uniformSelect, Function.comp]
  refine PMF.ext (λ x ↦ ?_)
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_fin, Nat.cast_add,
    Nat.cast_one, PMF.pure_apply, mul_ite, mul_one, mul_zero, PMF.ofMultiset_apply,
    Multiset.coe_count, Multiset.coe_card, Vector.toList_length]
  sorry

@[simp]
lemma support_uniformSelect [h : Selectable α β] (s : α) :
    ($ s).support = {x | x ∈ (h.elemVec s).toList} := sorry

@[simp]
lemma finSupport_uniformSelect [DecidableEq β] [h : Selectable α β] (s : α) :
    ($ s).finSupport = (h.elemVec s).toList.toFinset := sorry

@[simp]
lemma probOutput_uniformSelect [DecidableEq β] [h : Selectable α β] (s : α) (x : β) :
    [= x | $ s] = ((h.elemVec s).toList.count x) / (h.count s + 1 : ℝ≥0∞) := by
  simp [probOutput.def]
  congr
  refine funext (λ y ↦ funext (λ z ↦ ?_))
  sorry

@[simp]
lemma probEvent_uniformSelect [h : Selectable α β] (s : α)
    (p : β → Prop) [DecidablePred p] :
    [p | $ s] = ((h.elemVec s).toList.countP p) * (h.count s : ℝ≥0∞)⁻¹ := by
  sorry

end Selectable

/-- Select uniformly from a (non-empty) vector, by choosing a random index. -/
instance selectableVector (α : Type) (n : ℕ) [hn : NeZero n] :
    Selectable (Vector α n) α where
  count := λ _ ↦ n - 1
  elemVec := λ xs ↦ ⟨xs.1, symm (by simpa using Nat.succ_pred hn.out)⟩

/-- Select uniformly at random form a list by choosing a random index.
We require the type be inhabited so we can return a defualt value for empty lists. -/
instance selectableList (α : Type) [Inhabited α] :
    Selectable (List α) α where
  count := λ xs ↦ xs.length.pred
  elemVec := λ xs ↦ match xs with
    | [] => ⟨[default], rfl⟩
    | (x :: xs) => ⟨x :: xs, rfl⟩

/-- We can uniformly select from a finite set, but this is notably non-computable,
since we don't have a canonical ordering of the elements.
Generally selection from lists, vectors, etc. should be preferred. -/
noncomputable instance SelectableFinset (α : Type) [DecidableEq α] [Inhabited α] :
    Selectable (Finset α) α where
  count := λ s ↦ s.card.pred
  elemVec := λ s ↦ if h : s = ∅
    then ⟨[default], by simp [h]⟩
    else ⟨s.toList, by
      rw [Finset.length_toList]
      exact symm (Nat.succ_pred <| λ h' ↦ h (Finset.card_eq_zero.1 h'))⟩

section SelectableType

/-- A `SelectableType β` instance means that `β` is a finite inhabited type,
with an explicit list of the elements in the type.
We need to have an explicit vector, rather than just a `Finset` to make this computable. -/
-- class SelectableType (β : Type) extends Fintype β, Inhabited β where
--   elemVec : Vector β (Fintype.card β)
--   mem_elemVec : ∀ b : β, b ∈ elemVec.toList
class SelectableType (β : Type) extends Fintype β, Inhabited β where
  selectElem : OracleComp unifSpec β
  evelDist_selectElem : evalDist selectElem = PMF.uniformOfFintype β

def uniformOfFintype (β : Type) [h : SelectableType β] :
    OracleComp unifSpec β := h.selectElem

notation "$ᵗ" => uniformOfFintype

variables {α : Type} [SelectableType α]

@[simp]
lemma evalDist_uniformOfFintype : evalDist ($ᵗ α) = PMF.uniformOfFintype α := by
  have : ∀ x : α, x ∈ Fintype.elems := Fintype.complete
  simp [PMF.ext_iff, uniformOfFintype, Finset.univ, Fintype.card, this]
  sorry

@[simp]
lemma probOutput_uniformOfFintype [DecidableEq α] (x : α) :
    [= x | $ᵗ α] = (↑(Fintype.card α))⁻¹ := by
  simp [uniformOfFintype, Fintype.complete, Finset.univ, Fintype.card]
  sorry

@[simp]
lemma probEvent_uniformOfFintype (p : α → Prop) [DecidablePred p] :
    [p | $ᵗ α] = (Finset.univ.filter p).card / Fintype.card α := by
  simp [uniformOfFintype, Finset.univ, Fintype.card]
  sorry

end SelectableType

section instances

instance (α : Type) [Unique α] : SelectableType α where
  selectElem := return default
  evelDist_selectElem := by simpa [PMF.ext_iff] using Unique.eq_default

instance : SelectableType Bool where
  selectElem := $ [true, false]
  evelDist_selectElem := by
    simp [PMF.ext_iff]
    sorry

end instances

-- /-- `coinSpec` seen as a subset of `unifSpec`, choosing a random `Bool` uniformly. -/
-- noncomputable instance : coinSpec ⊂ₒ unifSpec where
--   toFun := λ () () ↦ $ᵗ Bool
--   evalDist_toFun' := λ i t ↦ sorry --by rw [evalDist_uniformOfFintype, evalDist_query i t]

-- end instances

end OracleComp
