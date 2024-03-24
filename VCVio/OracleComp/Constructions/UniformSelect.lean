/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist
import Mathlib.Data.Vector.Mem

/-!
# Selecting Uniformly From a Collection

This file defines some computations for selecting uniformly at random from a number
of different collections, using `unifSpec` to make the random choices.
-/

open OracleSpec

namespace OracleComp

section uniformOfVector

variable {α : Type} {n : ℕ}

/-- Select uniformly at random from a non-empty vector `v` by selecting a random index. -/
def uniformOfVector (v : Vector α (n + 1)) :
    OracleComp unifSpec α := v.get <$> $[0..n]

notation "$ᵛ" => uniformOfVector

@[simp]
lemma evalDist_uniformOfVector (v : Vector α (n + 1)) : evalDist ($ᵛ v) =
    PMF.ofMultiset (Multiset.ofList v.toList) (by simp [← List.length_eq_zero]) := by
  have : DecidableEq α := Classical.decEq α
  refine PMF.ext (λ x ↦ ?_)
  rw [← probOutput.def, uniformOfVector]
  -- simp
  rw [probOutput_map_eq_sum_filter_finSupport]
  simp [div_eq_mul_inv]
  congr
  rw [Finset.card_filter]
  sorry

@[simp]
lemma probOutput_uniformOfVector [BEq α] [LawfulBEq α] (v : Vector α (n + 1)) (x : α) :
    [= x | $ᵛ v] = v.toList.count x / (n + 1) := by
  simp [probOutput.def, evalDist_uniformOfVector, PMF.ofMultiset_apply, lawful_beq_subsingleton]






end uniformOfVector

section uniformOfFinset

variable {α : Type}

/-- Select uniformly at random from a non-empty finite set. This definition is noncomputable
because we need to use choice to convert the `Finset` into a `List`. -/
noncomputable def uniformOfFinset (s : Finset α) (hs : s.Nonempty) : OracleComp unifSpec α :=
  have hxs : s.toList ≠ [] := λ hxs ↦ hs.ne_empty <| Finset.toList_eq_nil.1 hxs
  $ᵛ ⟨s.toList, symm (Nat.succ_pred (λ h ↦ hxs <| List.length_eq_zero.1 h))⟩

notation "$ˢ" => uniformOfFinset

@[simp]
lemma evalDist_uniformOfFinset (s : Finset α) (hs : s.Nonempty) :
    evalDist ($ˢ s hs) = PMF.uniformOfFinset s hs := by
  refine PMF.ext (λ x ↦ ?_)
  sorry

@[simp]
lemma probOutput_uniformOfFinset [DecidableEq α] (s : Finset α) (hs : s.Nonempty) (x : α) :
    [= x | $ˢ s hs] = if x ∈ s then 1 / s.card else 0 := by
  sorry

end uniformOfFinset

section uniformOfFintype

/-- Select a random element from a non-empty finite type. This definition is noncomputable
because we need choice to construct a list of elements in the type. -/
noncomputable def uniformOfFintype (α : Type) [h : Fintype α] [Inhabited α] :
    OracleComp unifSpec α := $ˢ h.elems ⟨default, h.complete default⟩

notation "$ᵗ" => uniformOfFintype

variable (α : Type) [h : Fintype α] [Inhabited α]

@[simp]
lemma evalDist_uniformOfFintype : evalDist ($ᵗ α) = PMF.uniformOfFintype α := by
  sorry

@[simp]
lemma probOutput_uniformOfFintype (x : α) : [= x | $ᵗ α] = (↑(Fintype.card α))⁻¹ := by
  sorry

end uniformOfFintype

end OracleComp
