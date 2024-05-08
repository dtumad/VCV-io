/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist
import ToMathlib.General

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

@[simp]
lemma probOutput_uniformSelectList [DecidableEq α] (xs : List α) (x : α) :
    [= x | $ xs] = if xs.isEmpty then (if x = default then 1 else 0)
      else (↑(xs.count x) : ℝ≥0∞) / xs.length := by
  induction xs with
  | nil => simp only [uniformSelectList_nil, probOutput_pure, List.isEmpty_nil, ↓reduceIte,
      Nat.cast_ite, Nat.cast_one, CharP.cast_eq_zero]
  | cons y ys _ =>
      rw [probOutput_def, uniformSelectList_cons, List.count, ← List.countP_eq_sum_fin_ite,
        div_eq_mul_inv, Nat.cast_sum, Finset.sum_mul, List.isEmpty_cons]
      simp only [getElem_fin, List.getElem_eq_get, List.length_cons, Fin.eta, evalDist_map,
        evalDist_uniformFin, PMF.map_apply, PMF.uniformOfFintype_apply, Fintype.card_fin,
        Nat.cast_add, Nat.cast_one, ↓reduceIte, beq_iff_eq, Nat.cast_ite, CharP.cast_eq_zero,
        Nat.cast_succ, ite_mul, one_mul, zero_mul, tsum_fintype, @eq_comm _ x, zero_add, one_mul]

@[simp]
lemma probEvent_uniformSelectList (xs : List α) (p : α → Prop) [DecidablePred p] :
    [p | $ xs] = if xs.isEmpty then (if p default then 1 else 0)
      else (↑(xs.countP p) : ℝ≥0∞) / xs.length := by
  induction xs with
  | nil => simp only [uniformSelectList_nil, probEvent_pure, List.isEmpty_nil, ↓reduceIte]
  | cons y ys _ =>
      rw [probEvent_def, uniformSelectList_cons, ← List.countP_eq_sum_fin_ite,
          div_eq_mul_inv, Nat.cast_sum, Finset.sum_mul, List.isEmpty_cons]
      simp only [getElem_fin, List.getElem_eq_get, List.length_cons, Fin.eta, evalDist_map,
        evalDist_uniformFin, PMF.toOuterMeasure_map_apply, Set.preimage, Set.mem_def,
        PMF.toOuterMeasure_apply_fintype, Set.indicator, PMF.uniformOfFintype_apply,
        Fintype.card_fin, Nat.cast_add, Nat.cast_one, Set.mem_setOf_eq, ↓reduceIte,
        decide_eq_true_eq, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_succ, ite_mul,
        one_mul, zero_mul, zero_add, one_mul]
      congr
      ext x
      congr

end uniformSelectList

section uniformSelectVector

/-- Select a random element from a vector by indexing into it with a uniform value. -/
instance hasUniformSelectVector (α : Type) (n : ℕ) :
    HasUniformSelect (Vector α (n + 1)) α where
  uniformSelect := λ xs ↦ (xs[·]) <$> $[0..n]

variable {α : Type} {n : ℕ}

lemma uniformSelectVector_def (xs : Vector α (n + 1)) :
    ($ xs) = (xs[·]) <$> $[0..n] := rfl

/-- Uniform selection from a vector is exactly equal to uniform selection from the underlying list,
given some `Inhabited` instance on the output type. -/
lemma uniformSelectVector_eq_uniformSelectList [Inhabited α] (xs : Vector α (n + 1)) :
    ($ xs) = ($ xs.toList : OracleComp unifSpec α) :=
  match xs with
  | ⟨x :: xs, h⟩ => by
    have hxs : n = List.length xs := by simpa using symm h
    cases hxs
    simp [uniformSelectVector_def, uniformSelectList_cons,
      map_eq_bind_pure_comp, Function.comp, Vector.get]

@[simp]
lemma evalDist_uniformSelectVector (xs : Vector α (n + 1)) :
    evalDist ($ xs) = (PMF.uniformOfFintype (Fin (n + 1))).map (xs[·]) := by
  simp only [uniformSelectVector_def, getElem_fin, evalDist_map, evalDist_uniformFin]

@[simp]
lemma support_uniformSelectVector (xs : Vector α (n + 1)) :
    ($ xs).support = {x | x ∈ xs.toList} := by
  have : Inhabited α := ⟨xs.head⟩
  simp [uniformSelectVector_eq_uniformSelectList]

@[simp]
lemma finSupport_uniformSelectVector [DecidableEq α] (xs : Vector α (n + 1)) :
    ($ xs).finSupport = xs.toList.toFinset := by
  have : Inhabited α := ⟨xs.head⟩
  simp [uniformSelectVector_eq_uniformSelectList]

@[simp]
lemma probOutput_uniformSelectVector [DecidableEq α] (xs : Vector α (n + 1)) (x : α) :
    [= x | $ xs] = xs.toList.count x / (n + 1) := by
  have : Inhabited α := ⟨xs.head⟩
  simp [uniformSelectVector_eq_uniformSelectList]

@[simp]
lemma probEvent_uniformSelectVector (xs : Vector α (n + 1)) (p : α → Prop) [DecidablePred p] :
    [p | $ xs] = xs.toList.countP p / (n + 1) := by
  have : Inhabited α := ⟨xs.head⟩
  simp [uniformSelectVector_eq_uniformSelectList]

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

def uniformOfFintype (β : outParam Type) [Fintype β] [Inhabited β] [h : SelectableType β] :
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
