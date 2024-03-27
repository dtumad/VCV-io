/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.OracleSpec.SubSpec
import Mathlib.Data.Vector.Mem

/-!
# Selecting Uniformly From a Collection

This file defines some computations for selecting uniformly at random from a number
of different collections, using `unifSpec` to make the random choices.
-/

open OracleSpec OracleComp BigOperators

variable {spec : OracleSpec} {α β γ : Type}

namespace OracleComp

section uniformOfVector

/-- Select uniformly at random from a non-empty vector `v` by selecting a random index. -/
def uniformOfVector {n : ℕ} (v : Vector α (n + 1)) :
    OracleComp unifSpec α := v.get <$> $[0..n]

notation "$ᵛ" => uniformOfVector

variable {n : ℕ} (v : Vector α (n + 1))

@[simp]
lemma evalDist_uniformOfVector : evalDist ($ᵛ v) =
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
lemma probOutput_uniformOfVector [BEq α] [LawfulBEq α] (x : α) :
    [= x | $ᵛ v] = v.toList.count x / (n + 1) := by
  simp [probOutput.def, evalDist_uniformOfVector, PMF.ofMultiset_apply, lawful_beq_subsingleton]

@[simp]
lemma probEvent_uniformOfVector (p : α → Prop) [DecidablePred p] :
    [p | $ᵛ v] = (v.toList.filter p).length / (n + 1) := by
  sorry

end uniformOfVector

section uniformOfFinset

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
    [= x | $ˢ s hs] = if x ∈ s then (↑s.card)⁻¹ else 0 := by
  sorry

@[simp]
lemma probEvent_uniformOfFinset (s : Finset α) (hs : s.Nonempty) (p : α → Prop) [DecidablePred p] :
    [p | $ˢ s hs] = (s.filter p).card / s.card := by
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
  have : ∀ x : α, x ∈ Fintype.elems := Fintype.complete
  simp [PMF.ext_iff, uniformOfFintype, Finset.univ, Fintype.card, this]

@[simp]
lemma probOutput_uniformOfFintype [DecidableEq α] (x : α) :
    [= x | $ᵗ α] = (↑(Fintype.card α))⁻¹ := by
  simp [uniformOfFintype, Fintype.complete, Finset.univ, Fintype.card]

@[simp]
lemma probEvent_uniformOfFintype (p : α → Prop) [DecidablePred p] :
    [p | $ᵗ α] = (Finset.univ.filter p).card / Fintype.card α := by
  simp [uniformOfFintype, Finset.univ, Fintype.card]

end uniformOfFintype

end OracleComp

/-- Simulation oracle for replacing queries with uniform random selection, using `unifSpec`.
The resulting computation is still identical under `evalDist`.

The relevant `OracleSpec` can usually be inferred automatically, so we leave it implicit. -/
noncomputable def unifOracle {spec : OracleSpec} : spec →ₛₒ unifSpec :=
    statelessOracle (λ i _ ↦ $ᵗ (spec.range i))

namespace unifOracle

variable {spec : OracleSpec}

@[simp]
lemma apply_eq (i : spec.ι) : unifOracle i = λ _ ↦ ((., ())) <$> $ᵗ (spec.range i) := rfl

@[simp]
lemma evalDist_simulate (oa : OracleComp spec α) (u : Unit) :
    evalDist (simulate unifOracle oa u) = (evalDist oa).map ((., ())) := by
  revert u
  induction oa using OracleComp.inductionOn with
  | h_pure => simp only [simulate_pure, evalDist_pure, PMF.pure_map, forall_const]
  | h_query_bind i t oa hoa => simp [PMF.map, hoa]

@[simp]
lemma evalDist_simulate' (oa : OracleComp spec α) (u : Unit) :
    evalDist (simulate' unifOracle oa u) = evalDist oa :=
  by simpa [simulate', PMF.map_comp, Function.comp] using PMF.map_id (evalDist oa)

@[simp]
lemma probOutput_simulate (oa : OracleComp spec α) (u : Unit) (z : α × Unit) :
    [= z | simulate unifOracle oa u] = [= z.1 | oa] := by
  sorry

@[simp]
lemma probOutput_simulate' (oa : OracleComp spec α) (u : Unit) (x : α) :
    [= x | simulate' unifOracle oa u] = [= x | oa] := by
  sorry

@[simp]
lemma probEvent_simulate (oa : OracleComp spec α) (u : Unit) (p : α × Unit → Prop) :
    [p | simulate unifOracle oa u] = [λ x ↦ p (x, ()) | oa] := by
  sorry

@[simp]
lemma probEvent_simulate' (oa : OracleComp spec α) (u : Unit) (p : α → Prop) :
    [p | simulate' unifOracle oa u] = [p | oa] := by
  sorry

end unifOracle

section coinSpec

/-- `coinSpec` seen as a subset of `unifSpec`, choosing a random `Bool` uniformly. -/
noncomputable instance : coinSpec ⊂ₒ unifSpec where
  toFun := λ () () ↦ $ᵗ Bool
  evalDist_toFun' := λ i t ↦ by rw [evalDist_uniformOfFintype, evalDist_query i t]

end coinSpec
