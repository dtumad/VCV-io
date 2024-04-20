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

open OracleSpec

namespace OracleComp

/-- Typeclass to implement the notation `$ xs` for selecting an object uniformly from a collection.
The collection type is given by `cont` with the resulting type given by `β`. -/
class HasUniformSelect (cont : Type) (β : outParam Type) where
  uniformSelect : cont → OracleComp unifSpec β

/-- Given a selectable object, we can get a random element by indexing into the element vector. -/
def uniformSelect {cont : Type} (β : Type) [h : HasUniformSelect cont β] (xs : cont) :
    OracleComp unifSpec β := h.uniformSelect xs

prefix : 50 "$" => uniformSelect _

section uniformSelectVector

/-- Select a random element from a vector by indexing into it with a uniform value. -/
instance hasUniformSelectVector (α : Type) (n : ℕ) :
    HasUniformSelect (Vector α (n + 1)) α where
  uniformSelect := λ xs ↦ (xs[·]) <$> $[0..n]

end uniformSelectVector

section uniformSelectList

/-- Select a random element from a list by indexing into it with a uniform value.
If the list is empty we instead just return the default value from an `Inhabited` instance. -/
instance hasUniformSelectList (α : Type) [Inhabited α] :
    HasUniformSelect (List α) α where
  uniformSelect := λ xs ↦ match xs with
    | [] => return default
    | x :: xs => ((x :: xs)[·]) <$> $[0..xs.length]

variable (α : Type) [Inhabited α]

@[simp]
lemma uniformSelectList_nil : ($ ([] : List α) : OracleComp unifSpec α) = return default := rfl

lemma uniformSelectList_cons (x : α) (xs : List α) :
    ($ x :: xs : OracleComp unifSpec α) = ((x :: xs)[·]) <$> $[0..xs.length] := rfl

-- @[simp]
-- lemma evalDist_uniformSelectList (α : Type) [Inhabited α] (xs : List α) :
--     evalDist ($ xs : OracleComp unifSpec α) = PMF.ofMultiset (Multiset.ofList xs) _ :=
--   sorry

end uniformSelectList

section uniformSelectFinset

/-- Choose a random element from a finite set, by converting to a list and choosing from that.
This is noncomputable as we don't have a canoncial ordering for the resulting list,
so generally this should be avoided when possible. -/
noncomputable instance hasUniformSelectFinset (α : Type) [Inhabited α] :
    HasUniformSelect (Finset α) α where
  uniformSelect := λ s ↦ $ s.toList

end uniformSelectFinset

section SelectableType

/-- A `SelectableType β` instance means that `β` is a finite inhabited type,
with an explicit list of the elements in the type (usually some non-canonical choice).
We need to have an explicit vector, rather than just a `Finset` to make this computable. -/
class SelectableType (β : Type) extends Fintype β, Inhabited β where
  selectElem : OracleComp unifSpec β
  probOutput_selectElem (x : β) : [= x | selectElem] = (↑(Fintype.card β))⁻¹

def uniformOfFintype (β : Type) [h : SelectableType β] :
    OracleComp unifSpec β := h.selectElem

prefix : 90 "$ᵗ" => uniformOfFintype

@[simp]
lemma evalDist_uniformOfFintype (α : Type) [SelectableType α] :
    evalDist ($ᵗ α) = PMF.uniformOfFintype α := by
  simpa [PMF.ext_iff, uniformOfFintype, Finset.univ, Fintype.card] using
    SelectableType.probOutput_selectElem

@[simp]
lemma support_uniformOfFintype (α : Type) [SelectableType α] :
    ($ᵗ α).support = Set.univ := by
  simp [← support_evalDist]

@[simp]
lemma finSupport_uniformOfFintype (α : Type) [SelectableType α] [DecidableEq α] :
    ($ᵗ α).finSupport = Finset.univ := by
  simp [finSupport_eq_iff_support_eq_coe]

@[simp]
lemma probOutput_uniformOfFintype {α : Type} [SelectableType α] (x : α) :
    [= x | $ᵗ α] = (↑(Fintype.card α))⁻¹ := by
  simp only [probOutput, evalDist_uniformOfFintype, PMF.uniformOfFintype_apply]

@[simp]
lemma probEvent_uniformOfFintype {α : Type} [SelectableType α] (p : α → Prop) [DecidablePred p] :
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
