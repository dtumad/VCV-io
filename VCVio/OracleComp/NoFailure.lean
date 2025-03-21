/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.DistSemantics.Support

/-!
# Computations that Never Fail

This file defines a class `OracleComp.NoFailure` for computations that never fail regardless
of the behavior of oracles. This can be useful for simplifying some probability calculations.
-/

universe u v w

open OracleSpec

namespace OracleComp

variable {ι : Type*} {spec : OracleSpec ι}

def noFailure {α : Type u} (oa : OracleComp spec α) : Prop := by
  induction oa using OracleComp.construct with
  | pure _ => exact True
  | failure => exact False
  | query_bind _ _ r => exact ∀ x, r x

variable {α β γ : Type u}

lemma noFailure_eq_oracleComp_construct (oa : OracleComp spec α) :
    oa.noFailure = OracleComp.construct
      (fun _ ↦ True) (fun {β} _ _ r ↦ ∀ (x : β), r x) False oa := rfl

lemma noFailure_eq_freeMonad_construct (oa : OracleComp spec α) :
    oa.noFailure = FreeMonad.construct
      (fun t ↦ Option.rec False (fun _ ↦ True) t) (fun _ _ r ↦ ∀ x, r x) oa := rfl

@[simp]
lemma noFailure_pure (x : α) : noFailure (pure x : OracleComp spec α) := trivial

@[simp]
lemma noFailure_query (q : OracleQuery spec α) : noFailure (q : OracleComp spec α) :=
  fun _ => trivial

@[simp]
lemma noFailure_query_bind_iff {q : OracleQuery spec α} {oa : α → OracleComp spec β} :
    (liftM q >>= oa).noFailure ↔ ∀ x, noFailure (oa x) := Iff.rfl

alias ⟨noFailure_query_bind, _⟩ := noFailure_query_bind_iff

@[simp]
lemma not_noFailure_failure : ¬ noFailure (failure : OracleComp spec α) := fun h => h

@[simp]
lemma noFailure_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).noFailure ↔ oa.noFailure ∧ ∀ x ∈ oa.support, (ob x).noFailure := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | failure => simp
  | query_bind _ _ r ih => simp [ih, forall_and]; tauto

alias ⟨noFailure_bind, _⟩ := noFailure_bind_iff

@[simp]
lemma noFailure_map_iff (oa : OracleComp spec α) (f : α → β) :
    noFailure (f <$> oa) ↔ noFailure oa := by
  rw [map_eq_bind_pure_comp]
  simp only [noFailure_bind_iff, Function.comp_apply, noFailure_pure, implies_true, and_true]

@[simp]
instance {α : Type u} [spec.FiniteRange] : DecidablePred (@OracleComp.noFailure _ spec α) :=
  fun oa => by induction oa using OracleComp.construct' with
  | pure x => exact Decidable.isTrue (noFailure_pure x)
  | failure => exact Decidable.isFalse not_noFailure_failure
  | query_bind i t _ r =>
      simpa only [noFailure_bind_iff, noFailure_query, support_liftM, Set.mem_univ,
        forall_const, true_and] using Fintype.decidableForallFintype

section List

open List

/-- If each element of a list is mapped to a computation that never fails, then the computation
  obtained by monadic mapping over the list also never fails. -/
@[simp] lemma noFailure_list_mapM {f : α → OracleComp spec β} {as : List α}
    (h : ∀ x ∈ as, noFailure (f x)) : noFailure (mapM f as) := by
  induction as with
  | nil => simp only [mapM, mapM.loop, reverse_nil, noFailure_pure]
  | cons a as ih =>
    simp [mapM_cons, h]
    exact fun _ _ => ih (by simp at h; exact h.2)

@[simp] lemma noFailure_list_mapM' {f : α → OracleComp spec β} {as : List α}
    (h : ∀ x ∈ as, noFailure (f x)) : noFailure (mapM' f as) := by
  rw [mapM'_eq_mapM]
  exact noFailure_list_mapM h

@[simp] lemma noFailure_list_flatMapM {f : α → OracleComp spec (List β)} {as : List α}
    (h : ∀ x ∈ as, noFailure (f x)) : noFailure (flatMapM f as) := by
  induction as with
  | nil => simp only [flatMapM_nil, noFailure_pure]
  | cons a as ih =>
    simp only [flatMapM_cons, bind_pure_comp, noFailure_bind_iff, noFailure_map_iff]
    exact ⟨h a (by simp), fun y hy => ih (fun x hx => h x (by simp [hx]))⟩

@[simp] lemma noFailure_list_filterMapM {f : α → OracleComp spec (Option β)} {as : List α}
    (h : ∀ x ∈ as, noFailure (f x)) : noFailure (filterMapM f as) := by
  induction as with
  | nil => simp only [filterMapM_nil, noFailure_pure]
  | cons a as ih =>
    simp only [filterMapM_cons, bind_pure_comp, noFailure_bind_iff, noFailure_map_iff]
    refine ⟨h a (by simp), fun y hy => ?_⟩
    rcases y with _ | y <;> simp <;> exact ih (fun x hx => h x (by simp [hx]))

variable {s : Type v}

@[simp] lemma noFailure_list_foldlM {f : s → α → OracleComp spec s} {init : s} {as : List α}
    (h : ∀ i, ∀ x ∈ as, noFailure (f i x)) : noFailure (foldlM f init as) := by
  induction as generalizing init with
  | nil => simp only [foldlM, reverse_nil, noFailure_pure]
  | cons b bs ih =>
      simp only [foldlM_cons, noFailure_bind_iff, mem_cons, true_or, h, true_and]
      exact fun _ _ => ih (fun i x hx' => h i x (by simp [hx']))

@[simp] lemma noFailure_list_foldrM {f : α → s → OracleComp spec s} {init : s} {as : List α}
    (h : ∀ i, ∀ x ∈ as, noFailure (f x i)) : noFailure (foldrM f init as) := by
  induction as generalizing init with
  | nil => simp only [foldrM, reverse_nil, foldlM_nil, noFailure_pure]
  | cons b bs ih =>
      simp only [foldrM_cons, noFailure_bind_iff]
      exact ⟨ih (fun i x hx => h i x (by simp [hx])), fun y _ => h y b (by simp)⟩

-- TODO: add lemmas for more monadic list operations

end List

section List.Vector

variable {n : ℕ}

@[simp] lemma noFailure_list_vector_mmap {f : α → OracleComp spec β} {as : List.Vector α n}
    (h : ∀ x ∈ as.toList, noFailure (f x)) : noFailure (List.Vector.mmap f as) := by
  induction as with
  | nil => simp only [List.Vector.mmap, noFailure_pure]
  | @cons n x xs ih =>
    simp only [List.Vector.mmap_cons, bind_pure_comp, noFailure_bind_iff, noFailure_map_iff]
    exact ⟨h x (by simp), fun y hy => ih (fun x' hx' => h x' (by simp [hx']))⟩

end List.Vector

section Array

open Array

@[simp] lemma noFailure_array_mapM {f : α → OracleComp spec β} {as : Array α}
    (h : ∀ x ∈ as, noFailure (f x)) : noFailure (mapM f as) := by
  induction ha : as.toList generalizing as with
  | nil => simp_all [h, Array.mapM, mapM.map, noFailure_pure]
  | cons x xs ih =>
    simp_rw [mapM_eq_mapM_toList, ha] at ih ⊢
    simp at ih ⊢
    -- boring case analysis
    sorry

end Array

section Vector

open Vector

variable {n : ℕ}

-- Need induction principle for vectors
@[simp] lemma noFailure_vector_mapM {f : α → OracleComp spec β} {xs : Vector α n}
    (h : ∀ x ∈ xs.toList, noFailure (f x)) : noFailure (mapM f xs) := by sorry
  -- match h : xs with
  -- | ⟨⟨[]⟩, _⟩ => simp [Vector.mapM, Vector.mapM.go, noFailure_pure]
  -- | ⟨⟨x :: xs⟩, _⟩ =>
  --   simp only [mapM_cons, bind_pure_comp, noFailure_bind_iff, noFailure_map_iff]
  --   exact ⟨h x (by simp), fun y hy => ih (fun x' hx' => h x' (by simp [hx']))⟩

end Vector

end OracleComp
