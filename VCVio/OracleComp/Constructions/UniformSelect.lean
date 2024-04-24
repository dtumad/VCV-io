/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
-- import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.DistSemantics.EvalDist
import Mathlib.Data.Vector.Mem

/-!
# Selecting Uniformly From a Collection

This file defines some computations for selecting uniformly at random from a number
of different collections, using `unifSpec` to make the random choices.
-/

open OracleSpec BigOperators ENNReal

namespace OracleComp

/-- Typeclass to implement the notation `$ xs` for selecting an object uniformly from a collection.
The container type is given by `cont` with the resulting type given by `β`. -/
class HasUniformSelect (cont : Type) (β : outParam Type) where
  uniformSelect : cont → OracleComp unifSpec β

/-- Given a selectable object, we can get a random element by indexing into the element vector. -/
def uniformSelect {cont : Type} (β : Type) [h : HasUniformSelect cont β] (xs : cont) :
    OracleComp unifSpec β := h.uniformSelect xs

prefix : 50 "$" => uniformSelect _

section uniformSelectList

/-- Select a random element from a list by indexing into it with a uniform value.
If the list is empty we instead just return the default value from an `Inhabited` instance.
This means selecting from a vector is often preferable, as we can prove at the type level
that there is an element in the list, avoiding the defualt case on empty lists. -/
instance hasUniformSelectList (α : Type) [Inhabited α] :
    HasUniformSelect (List α) α where
  uniformSelect := λ xs ↦ match xs with
    | [] => return default
    | x :: xs => ((x :: xs)[·]) <$> $[0..xs.length]

variable {α : Type} [Inhabited α]

@[simp]
lemma uniformSelectList_nil (α : Type) [Inhabited α] :
  ($ ([] : List α) : OracleComp unifSpec α) = return default := rfl

lemma uniformSelectList_cons (x : α) (xs : List α) :
    ($ x :: xs : OracleComp unifSpec α) = ((x :: xs)[·]) <$> $[0..xs.length] := rfl

@[simp]
lemma evalDist_uniformSelectList (xs : List α) :
    evalDist ($ xs) = match xs with
      | [] => PMF.pure default
      | x :: xs => (PMF.uniformOfFintype (Fin xs.length.succ)).map ((x :: xs)[·]) := by
  match xs with
  | [] => rfl
  | x :: xs => simp only [uniformSelectList_cons, getElem_fin, List.getElem_eq_get,
      List.length_cons, Fin.eta, evalDist_map, evalDist_uniformFin]

@[simp]
lemma support_uniformSelectList (xs : List α) :
    ($ xs).support = if xs.isEmpty then {default} else {y | y ∈ (xs)} := by
  match xs with
    | [] => rfl
    | x :: xs => simp [uniformSelectList_cons, Set.ext_iff, List.mem_iff_get]

@[simp]
lemma finSupport_uniformSelectList [DecidableEq α] (xs : List α) :
    ($ xs).finSupport = if xs.isEmpty then {default} else xs.toFinset := by
  split_ifs with h <;> simp only [finSupport_eq_iff_support_eq_coe, support_uniformSelectList,
    h, ↓reduceIte, List.coe_toFinset, Finset.coe_singleton]

-- port

end uniformSelectList

section uniformSelectVector

/-- Select a random element from a vector by indexing into it with a uniform value. -/
instance hasUniformSelectVector (α : Type) (n : ℕ) :
    HasUniformSelect (Vector α (n + 1)) α where
  uniformSelect := λ xs ↦ (xs[·]) <$> $[0..n]

variable {α : Type} {n : ℕ}

lemma uniformSelectVector_def (xs : Vector α (n + 1)) :
  ($ xs) = (xs[·]) <$> $[0..n] := rfl

@[simp]
lemma evalDist_uniformSelectVector (xs : Vector α (n + 1)) :
    evalDist ($ xs) = (PMF.uniformOfFintype (Fin (n + 1))).map (xs[·]) := by
  simp only [uniformSelectVector_def, getElem_fin, evalDist_map, evalDist_uniformFin]

@[simp]
lemma support_uniformSelectVector (xs : Vector α (n + 1)) :
    ($ xs).support = {x | x ∈ xs.toList} := by
  refine Set.ext (λ x ↦ ?_)
  simp only [uniformSelectVector_def, getElem_fin, support_map, support_uniformFin, Set.image_univ,
    Set.mem_range, Vector.mem_iff_get, Set.mem_setOf_eq]
  rfl

@[simp]
lemma finSupport_uniformSelectVector [DecidableEq α] (xs : Vector α (n + 1)) :
    ($ xs).finSupport = xs.toList.toFinset := by
  simp only [finSupport_eq_iff_support_eq_coe, support_uniformSelectVector, List.coe_toFinset]

@[simp]
lemma probOutput_uniformSelectVector [DecidableEq α] (xs : Vector α (n + 1)) (x : α) :
    [= x | $ xs] = xs.toList.count x / (n + 1) := by
  simp [probOutput_def]
  rw [List.count, ← List.countP_eq_sum_fin_ite]
  rw [div_eq_mul_inv, Nat.cast_sum, Finset.sum_mul]
  rw [tsum_eq_sum (s := Finset.univ) (by simp)]
  have : n + 1 = List.length (Vector.toList xs) := by simp
  apply Finset.sum_bij' (λ i _ ↦ by convert i; simp)
    (λ i _ ↦ by convert i)
  · simp
  · simp
  · intros i hi
    -- rw [Vector.instGetElemVectorNatLtInstLTNat]
    simp [Vector.get, @eq_comm _ x]
    congr
    simp
    simp
  · simp
  · simp

-- @[simp]
-- lemma probEvent_uniformSelectVector [DecidableEq α] (xs : Vector α (n + 1)) (p : α → Prop) :
--     [p | $ xs] = xs.toList.countP

end uniformSelectVector

section uniformSelectFinset

/-- Choose a random element from a finite set, by converting to a list and choosing from that.
This is noncomputable as we don't have a canoncial ordering for the resulting list,
so generally this should be avoided when possible. -/
noncomputable instance hasUniformSelectFinset (α : Type) [Inhabited α] :
    HasUniformSelect (Finset α) α where
  uniformSelect := λ s ↦ $ s.toList

-- port

end uniformSelectFinset

section SelectableType

/-- A `SelectableType β` instance means that `β` is a finite inhabited type,
with an explicit list of the elements in the type (usually some non-canonical choice).
We need to have an explicit vector, rather than just a `Finset` to make this computable. -/
class SelectableType (β : Type) [Fintype β] [Inhabited β] where
  selectElem : OracleComp unifSpec β
  probOutput_selectElem (x : β) : [= x | selectElem] = (↑(Fintype.card β))⁻¹

def uniformOfFintype (β : Type) [Fintype β] [Inhabited β] [h : SelectableType β] :
    OracleComp unifSpec β := h.selectElem

prefix : 90 "$ᵗ" => uniformOfFintype

variable (α : Type) [Fintype α] [Inhabited α] [SelectableType α]

@[simp]
lemma evalDist_uniformOfFintype : evalDist ($ᵗ α) = PMF.uniformOfFintype α := by
  simpa [PMF.ext_iff, uniformOfFintype, Finset.univ, Fintype.card] using
    SelectableType.probOutput_selectElem

@[simp]
lemma support_uniformOfFintype : ($ᵗ α).support = Set.univ := by
  simp [← support_evalDist]

@[simp]
lemma finSupport_uniformOfFintype [DecidableEq α] : ($ᵗ α).finSupport = Finset.univ := by
  simp [finSupport_eq_iff_support_eq_coe]

@[simp]
lemma probOutput_uniformOfFintype (x : α) : [= x | $ᵗ α] = (↑(Fintype.card α))⁻¹ := by
  simp only [probOutput, evalDist_uniformOfFintype, PMF.uniformOfFintype_apply]

@[simp]
lemma probEvent_uniformOfFintype (p : α → Prop) [DecidablePred p] :
    [p | $ᵗ α] = (Finset.univ.filter p).card / Fintype.card α := by
  simp [probEvent_eq_sum_filter_univ, div_eq_mul_inv]

section instances

instance (α : Type) [Unique α] : SelectableType α where
  selectElem := return default
  probOutput_selectElem := by simpa using Unique.eq_default

instance : SelectableType Bool where
  selectElem := $ [false, true]
  probOutput_selectElem := λ b ↦ match b with
    | true => by
        have : 1 ∉ Finset.range 1 := by simp
        simp only [uniformSelectList_cons, List.length_singleton,
          probOutput_map_eq_sum_filter_finSupport, finSupport_uniformFin, probOutput_uniformFin,
          Nat.cast_one, Finset.sum_const, nsmul_eq_mul, Fintype.card_bool, Nat.cast_ofNat,
          Finset.card_filter, Finset.sum_fin_eq_sum_range, Finset.range_succ,
          Finset.sum_insert this]
        simpa [getElem] using one_add_one_eq_two
    | false => by
        have : 1 ∉ Finset.range 1 := by simp
        simp only [uniformSelectList_cons, List.length_singleton,
          probOutput_map_eq_sum_filter_finSupport, finSupport_uniformFin, probOutput_uniformFin,
          Nat.cast_one, Finset.sum_const, nsmul_eq_mul, Fintype.card_bool, Nat.cast_ofNat,
          Finset.card_filter, Finset.sum_fin_eq_sum_range, Finset.range_succ,
          Finset.sum_insert this]
        simpa [getElem] using one_add_one_eq_two

end instances

end SelectableType

end OracleComp
