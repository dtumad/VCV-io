/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.Prod
import ToMathlib.General

/-!
# Selecting Uniformly From a Collection

This file defines some computations for selecting uniformly at random from a number
of different collections, using `unifSpec` to make the random choices.

TODO: A lot of lemmas here could exist at the `PMF` level instead.
Probably even a lot of the uniform constructions themselves (like `uniformOfList`)
-/

open Mathlib OracleSpec BigOperators ENNReal

namespace OracleComp

section uniformSelect

/-- Typeclass to implement the notation `$ xs` for selecting an object uniformly from a collection.
The container type is given by `cont` with the resulting type given by `β`.
NOTE: This current implementation doesn't impose any "correctness" conditions,
it purely exists to provide the notation similar to `Mul` -/
class HasUniformSelect (cont : Type) (β : outParam Type) [DecidableEq β] where
  uniformSelect : cont → ProbComp β

/-- Given a selectable object, we can get a random element by indexing into the element vector. -/
def uniformSelect {cont : Type} (β : Type) [DecidableEq β]
    [h : HasUniformSelect cont β] (xs : cont) : ProbComp β :=
  h.uniformSelect xs

prefix : 50 "$" => uniformSelect _

variable {cont β : Type} [DecidableEq β] [h : HasUniformSelect cont β]

end uniformSelect

section uniformSelectList

/-- Select a random element from a list by indexing into it with a uniform value.
If the list is empty we instead just return the default value from an `Inhabited` instance.
This means selecting from a vector is often preferable, as we can prove at the type level
that there is an element in the list, avoiding the defualt case on empty lists. -/
instance hasUniformSelectList (α : Type) [Inhabited α] [DecidableEq α] :
    HasUniformSelect (List α) α where
  uniformSelect := λ xs ↦ match xs with
    | [] => return default
    | x :: xs => ((x :: xs)[·]) <$> $[0..xs.length]

variable {α : Type} [Inhabited α] [DecidableEq α]

@[simp]
lemma uniformSelectList_nil : ($ ([] : List α) : ProbComp α) = return default := rfl

lemma uniformSelectList_cons (x : α) (xs : List α) :
    ($ x :: xs : ProbComp α) = ((x :: xs)[·]) <$> $[0..xs.length] := rfl

@[simp]
lemma evalDist_uniformSelectList (xs : List α) :
    evalDist ($ xs) = match xs with
    | [] => PMF.pure (some default)
    | x :: xs => (PMF.uniformOfFintype (Fin xs.length.succ)).map (some (x :: xs)[·]) := by
  match xs with
  | [] => rfl
  | x :: xs => simp only [uniformSelectList_cons, Fin.getElem_fin, evalDist_map,
      evalDist_uniformFin, PMF.map_comp, Option.map_comp_some, Nat.succ_eq_add_one]; rfl

  -- simp only [uniformSelectList_cons, Fin.getElem_fin, List.getElem?_eq_getElem,
  --     List.length_cons, Fin.eta, evalDist_map, evalDist_uniformFin]

@[simp]
lemma support_uniformSelectList (xs : List α) :
    ($ xs).support = if xs.isEmpty then {default} else {y | y ∈ (xs)} := by
  match xs with
    | [] => rfl
    | x :: xs => simp only [uniformSelectList_cons, Fin.getElem_fin, support_map,
        support_uniformFin, Set.image_univ, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.mem_iff_get, List.length_cons, List.get_eq_getElem, Set.ext_iff, Set.mem_range,
        Set.mem_setOf_eq, implies_true]

@[simp]
lemma finSupport_uniformSelectList (xs : List α) :
    ($ xs).finSupport = if xs.isEmpty then {default} else xs.toFinset := by
  split_ifs with h <;> simp only [finSupport_eq_iff_support_eq_coe, support_uniformSelectList,
    h, ↓reduceIte, List.coe_toFinset, Finset.coe_singleton, Bool.false_eq_true]

@[simp]
lemma probOutput_uniformSelectList (xs : List α) (x : α) :
    [= x | $ xs] = if xs.isEmpty then (if x = default then 1 else 0)
      else (↑(xs.count x) : ℝ≥0∞) / xs.length := by
  induction xs with
  | nil => simp only [uniformSelectList_nil, probOutput_pure, List.isEmpty_nil, ↓reduceIte,
      Nat.cast_ite, Nat.cast_one, CharP.cast_eq_zero]
  | cons y ys _ =>
      sorry
      -- rw [probOutput_def, uniformSelectList_cons, List.count, ← List.countP_eq_sum_fin_ite,
      --   div_eq_mul_inv, Nat.cast_sum, Finset.sum_mul, List.isEmpty_cons]
      -- simp only [Fin.getElem_fin, evalDist_map, evalDist_uniformFin, PMF.map_apply, @eq_comm _ x,
      --   PMF.uniformOfFintype_apply, Fintype.card_fin, Nat.cast_succ, tsum_fintype,
      --   Finset.sum_boole', nsmul_eq_mul, Bool.false_eq_true, ↓reduceIte, List.length_cons,
      --   beq_iff_eq, Nat.cast_ite, CharP.cast_eq_zero, zero_add, ite_mul, one_mul, zero_mul]

@[simp]
lemma probEvent_uniformSelectList (xs : List α) (p : α → Prop) [DecidablePred p] :
    [p | $ xs] = if xs.isEmpty then (if p default then 1 else 0)
      else (↑(xs.countP p) : ℝ≥0∞) / xs.length := by
  induction xs with
  | nil => simp only [uniformSelectList_nil, probEvent_pure, List.isEmpty_nil, ↓reduceIte]
  | cons y ys _ =>
      rw [probEvent_def, uniformSelectList_cons, ← List.countP_eq_sum_fin_ite,
          div_eq_mul_inv, Nat.cast_sum, Finset.sum_mul, List.isEmpty_cons]
      simp only [Fin.getElem_fin, List.getElem?_eq_getElem, List.length_cons, Fin.eta, evalDist_map,
        evalDist_uniformFin, PMF.toOuterMeasure_map_apply, Set.preimage, Set.mem_def,
        PMF.toOuterMeasure_apply_fintype, Set.indicator, PMF.uniformOfFintype_apply,
        Fintype.card_fin, Nat.cast_add, Nat.cast_one, Set.mem_setOf_eq, ↓reduceIte,
        decide_eq_true_eq, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_succ, ite_mul,
        one_mul, zero_mul, zero_add, one_mul]
      -- congr
      sorry
      -- ext x
      -- congr

end uniformSelectList

section uniformSelectVector

/-- Select a random element from a vector by indexing into it with a uniform value. -/
instance hasUniformSelectVector (α : Type) [DecidableEq α] (n : ℕ) :
    HasUniformSelect (Mathlib.Vector α (n + 1)) α where
  uniformSelect := λ xs ↦ (xs[·]) <$> $[0..n]

lemma uniformSelectVector_def {α : Type} [DecidableEq α] {n : ℕ} (xs : Mathlib.Vector α (n + 1)) :
    ($ xs) = (xs[·]) <$> $[0..n] := rfl

variable {α : Type} [DecidableEq α] {n : ℕ}

/-- Uniform selection from a vector is exactly equal to uniform selection from the underlying list,
given some `Inhabited` instance on the output type. -/
lemma uniformSelectVector_eq_uniformSelectList (xs : Mathlib.Vector α (n + 1)) :
    let _ :  Inhabited α := ⟨xs.head⟩; ($ xs) = ($ xs.toList : ProbComp α) :=
  match xs with
  | ⟨x :: xs, h⟩ => by
    have hxs : n = List.length xs := by simpa using symm h
    cases hxs
    simp only [uniformSelectVector_def, Fin.getElem_fin, Vector.getElem_eq_get, Vector.get,
      List.length_cons, Fin.eta, Fin.cast_eq_self, List.get_eq_getElem, map_eq_bind_pure_comp,
      Function.comp, Vector.toList_mk, uniformSelectList_cons]
    sorry

@[simp]
lemma evalDist_uniformSelectVector (xs : Mathlib.Vector α (n + 1)) :
    evalDist ($ xs) = (PMF.uniformOfFintype (Fin (n + 1))).map (xs[·]) := by
  simp only [uniformSelectVector_def, Fin.getElem_fin, evalDist_map, evalDist_uniformFin]
  sorry

@[simp]
lemma support_uniformSelectVector (xs : Mathlib.Vector α (n + 1)) :
    ($ xs).support = {x | x ∈ xs.toList} := by
  simp only [uniformSelectVector_eq_uniformSelectList, support_uniformSelectList,
    Vector.empty_toList_eq_ff, Bool.false_eq_true, ↓reduceIte]

@[simp]
lemma finSupport_uniformSelectVector (xs : Mathlib.Vector α (n + 1)) :
    ($ xs).finSupport = xs.toList.toFinset := by
  simp only [uniformSelectVector_eq_uniformSelectList, finSupport_uniformSelectList,
    Vector.empty_toList_eq_ff, Bool.false_eq_true, ↓reduceIte]

@[simp]
lemma probOutput_uniformSelectVector (xs : Mathlib.Vector α (n + 1)) (x : α) :
    [= x | $ xs] = xs.toList.count x / (n + 1) := by
  simp only [uniformSelectVector_eq_uniformSelectList, probOutput_uniformSelectList,
    Vector.empty_toList_eq_ff, Bool.false_eq_true, ↓reduceIte, Vector.toList_length, Nat.cast_add,
    Nat.cast_one]

@[simp]
lemma probEvent_uniformSelectVector (xs : Mathlib.Vector α (n + 1)) (p : α → Prop) [DecidablePred p] :
    [p | $ xs] = xs.toList.countP p / (n + 1) := by
  simp only [uniformSelectVector_eq_uniformSelectList, probEvent_uniformSelectList,
    Vector.empty_toList_eq_ff, Bool.false_eq_true, ↓reduceIte, Vector.toList_length, Nat.cast_add,
    Nat.cast_one]

end uniformSelectVector

section uniformSelectFinset

/-- Choose a random element from a finite set, by converting to a list and choosing from that.
This is noncomputable as we don't have a canoncial ordering for the resulting list,
so generally this should be avoided when possible. -/
noncomputable instance hasUniformSelectFinset (α : Type) [Inhabited α] [DecidableEq α] :
    HasUniformSelect (Finset α) α where
  uniformSelect := λ s ↦ $ s.toList

lemma uniformSelectFinset_def {α : Type} [Inhabited α] [DecidableEq α] (s : Finset α) :
    ($ s) = ($ s.toList) := rfl

variable {α : Type} [Inhabited α]

@[simp]
lemma support_uniformSelectFinset [DecidableEq α] (s : Finset α) :
    ($ s).support = if s.Nonempty then ↑s else {default} := by
  simp only [Finset.nonempty_iff_ne_empty, ne_eq, ite_not]
  split_ifs with hs <;> simp [hs, uniformSelectFinset_def]

@[simp]
lemma finSupport_uniformSelectFinset [DecidableEq α] (s : Finset α) :
    ($ s).finSupport = if s.Nonempty then s else {default} := by
  split_ifs with hs <;> simp only [hs, finSupport_eq_iff_support_eq_coe,
    support_uniformSelectFinset, if_true, if_false, Finset.coe_singleton]

@[simp]
lemma evalDist_uniformSelectFinset [DecidableEq α] (s : Finset α) :
    evalDist ($ s) = if hs : s.Nonempty then PMF.uniformOfFinset s hs else PMF.pure default := by
  rw [uniformSelectFinset_def, evalDist_uniformSelectList]
  split_ifs with hs
  · have : s.toList ≠ [] := by simp only [ne_eq, Finset.toList_eq_nil, ←
      Finset.nonempty_iff_ne_empty, hs]
    refine PMF.ext (λ y ↦ ?_)
    obtain ⟨x, xs, hxs⟩ := List.exists_cons_of_ne_nil this
    simp only [hxs, Nat.succ_eq_add_one, Fin.getElem_fin, PMF.map_apply, Fintype.card_fin,
      PMF.uniformOfFintype_apply, Nat.cast_add, Nat.cast_one,
      PMF.uniformOfFinset_apply, tsum_fintype]
    rw [Finset.sum_boole']
    have : (xs.length + 1 : ℝ≥0∞)⁻¹ = ((x :: xs).length : ℝ≥0∞)⁻¹ := by simp
    simp only [← hxs, this, Finset.length_toList, nsmul_eq_mul]
    sorry
    -- split_ifs with hs
    -- · convert (one_mul _)
    --   rw [Nat.cast_eq_one]
    --   simp_rw [hxs, @eq_comm _ y]
    --   refine ((List.card_filter_getElem_eq (x :: xs ) y)).trans ?_
    --   rw [← hxs]
    --   rw [Finset.count_toList]
    --   simp only [hs, ↓reduceIte]
    -- · convert (zero_mul _)
    --   simp only [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.ext_iff, Finset.mem_filter,
    --     Finset.mem_univ, true_and, Finset.not_mem_empty, iff_false]
    --   refine λ i hi ↦ hs ?_
    --   rw [hi, ← Finset.mem_toList]
    --   exact List.getElem_mem _
  · rw [Finset.nonempty_iff_ne_empty, not_not] at hs
    simp only [hs, Finset.toList_empty]
    sorry

@[simp]
lemma probOutput_uniformSelectFinset [DecidableEq α] (s : Finset α) (x : α) :
    [= x | $ s] = if x ∈ s then (s.card : ℝ≥0∞)⁻¹ else if s.Nonempty then 0
      else if x = default then 1 else 0 := by
  sorry
  -- split_ifs with hx hs hxd
  -- · have hs' : s.Nonempty := ⟨x, hx⟩
  --   simp only [probOutput_def, evalDist_uniformSelectFinset, hs', ↓reduceDIte,
  --     PMF.uniformOfFinset_apply, hx, ↓reduceIte]
  -- · simp only [probOutput_eq_zero_iff', finSupport_uniformSelectFinset, hs, ↓reduceIte, hx,
  --     not_false_eq_true]
  -- · simp only [hxd, probOutput_eq_one_iff', finSupport_uniformSelectFinset, hs, ↓reduceIte,
  --     subset_refl]
  -- · simp only [probOutput_eq_zero_iff', finSupport_uniformSelectFinset, hs, ↓reduceIte,
  --     Finset.mem_singleton, hxd, not_false_eq_true]

end uniformSelectFinset

section SelectableType

/-- A `SelectableType β` instance means that `β` is a finite inhabited type,
with a computation `selectElem` that selects uniformly at random from the type.
This generally requires choosing some "canonical" ordering for the type,
so we include this to get a computable version of selection.
We also require that each element has the same probability of being chosen from by `selectElem`,
see `SelectableType.probOutput_selectElem` for the reduction when `α` has a fintype instance. -/
class SelectableType (β : Type) where
  selectElem : ProbComp β
  probOutput_selectElem_eq (x y : β) :
    [= x | selectElem] = [= y | selectElem]

def uniformOfFintype (β : Type) [h : SelectableType β] :
    ProbComp β := h.selectElem

prefix : 90 "$ᵗ" => uniformOfFintype

variable (α : Type) [hα : SelectableType α]

/-- Because all -/
lemma SelectableType.probOutput_selectElem {α : Type} [Fintype α]
    [h : SelectableType α] (x : α) : [= x | $ᵗ α] = (↑(Fintype.card α) : ℝ≥0∞)⁻¹ := by
  have : (Fintype.card α : ℝ≥0∞) = ∑ y : α, 1 :=
    by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  simp_rw [this, Finset.mul_sum, mul_one]
  -- refine tsum_probOutput
  sorry
  -- exact (Finset.sum_congr rfl <| λ y _ ↦ h.probOutput_selectElem_eq x y).trans
  --   (sum_probOutput ($ᵗ α))

@[simp]
lemma evalDist_uniformOfFintype [Inhabited α] [Fintype α] :
    evalDist ($ᵗ α) = PMF.uniformOfFintype α := by
  sorry
  -- simpa [PMF.ext_iff, uniformOfFintype, Finset.univ, Fintype.card] using
  --   SelectableType.probOutput_selectElem

@[simp]
lemma support_uniformOfFintype [Fintype α] : ($ᵗ α).support = Set.univ := by
  sorry
  -- have : Inhabited α := ⟨hα.selectElem.defaultResult⟩
  -- simp only [← support_evalDist, evalDist_uniformOfFintype, PMF.support_uniformOfFintype,
  --   Set.top_eq_univ]

@[simp]
lemma finSupport_uniformOfFintype [Fintype α] [DecidableEq α] :
    ($ᵗ α).finSupport = Finset.univ := by
  simp only [finSupport_eq_iff_support_eq_coe, support_uniformOfFintype, Finset.coe_univ]

@[simp]
lemma probOutput_uniformOfFintype [Fintype α] (x : α) :
    [= x | $ᵗ α] = (↑(Fintype.card α))⁻¹ := by
  sorry
  -- have : Inhabited α := ⟨hα.selectElem.defaultResult⟩
  -- simp only [probOutput, evalDist_uniformOfFintype, PMF.uniformOfFintype_apply]

@[simp]
lemma probEvent_uniformOfFintype [Fintype α] (p : α → Prop) [DecidablePred p] :
    [p | $ᵗ α] = (Finset.univ.filter p).card / Fintype.card α := by
  simp only [probEvent_eq_sum_filter_univ, probOutput_uniformOfFintype, Finset.sum_const,
    nsmul_eq_mul, div_eq_mul_inv]

section instances

instance (α : Type) [Unique α] : SelectableType α where
  selectElem := return default
  probOutput_selectElem_eq x y := by rw [Unique.eq_default x, Unique.eq_default y]

instance : SelectableType Bool where
  selectElem := $ [false, true]
  probOutput_selectElem_eq x y := by simp

instance (α β : Type) [Fintype α] [Fintype β] [Inhabited α] [Inhabited β]
    [SelectableType α] [SelectableType β] : SelectableType (α × β) where
  selectElem := (·, ·) <$> ($ᵗ α) <*> ($ᵗ β)
  probOutput_selectElem_eq:= by simp only [Prod.forall, probOutput_seq_map_prod_mk_eq_mul,
    probOutput_uniformOfFintype, forall_const, implies_true]

/-- Nonempty `Fin` types can be selected from, using implicit casting of `Fin (n - 1 + 1)`. -/
instance (n : ℕ) : SelectableType (Fin (n + 1)) where
  selectElem := $[0..n]
  probOutput_selectElem_eq x y := by simp only [probOutput_uniformFin, implies_true]

/-- Version of `Fin` selection using the `NeZero` typeclass, avoiding the need for `n + 1` form.
TODO: cleanup -/
instance (n : ℕ) [hn : NeZero n] : SelectableType (Fin n) where
  selectElem := congr_arg Fin (Nat.succ_pred (NeZero.ne n)).symm ▸ $ᵗ (Fin (n - 1 + 1))
  probOutput_selectElem_eq x y := by simp [probOutput_eqRec]

end instances

end SelectableType

end OracleComp
