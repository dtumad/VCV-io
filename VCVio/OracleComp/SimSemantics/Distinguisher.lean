/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Append

/-!
# Distinguishers for Query Implementations

This file defines the type `QueryImpl.Distinguisher spec` of distinguishers for a
pair of oracle implementations, as a computation returning a `Bool` with those oracles.
`DistinguisherExperiment` runs one on a pair of computations.

We also define a predicate `DistinguisherBound` to specify a bound on the chance of success.
-/

open OracleComp OracleSpec ENNReal

variable {ι : Type _} {spec : OracleSpec ι} {α β γ : Type _}

/-- A (randomized) distinguisher for the oracles in the interface `spec` is a computation
that is given access to oracles in `spec` and "guesses" an implementation via its return value.
We don't include the implementations it is distinguishing here, a "good" distinguisher for
two implementation could equally be viewed as a "bad" distinguisher for two others. -/
def Distinguisher (spec : OracleSpec ι) :=
  OracleComp (unifSpec ++ₒ spec) Bool

namespace QueryImpl

/-- Two `QueryImpl` are interchangeable if they always induce the same chance of a distinguisher
returning `true` and `false` with those implementations.
We include both conditions to factor in the chance of `adv` resulting in `failure`. -/
def Interchangeable (impl₁ impl₂ : QueryImpl spec ProbComp) : Prop :=
  ∀ adv : Distinguisher spec,
    [= true | simulateR impl₁ adv] = [= true | simulateR impl₂ adv] ∧
      [= false | simulateR impl₁ adv] = [= false | simulateR impl₂ adv]

infixr:25 " ≃ₛₒ " => Interchangeable

instance : IsEquiv (QueryImpl spec ProbComp) Interchangeable where
  refl _ _ := ⟨rfl, rfl⟩
  symm _ _ h adv := ⟨(h adv).1.symm, (h adv).2.symm⟩
  trans _ _ _ h₁ h₂ adv := ⟨(h₁ adv).1.trans (h₂ adv).1, (h₁ adv).2.trans (h₂ adv).2⟩

lemma interchangeable_def (impl₁ impl₂ : QueryImpl spec ProbComp) :
    impl₁ ≃ₛₒ impl₂ ↔ ∀ adv : Distinguisher spec,
      [= true | simulateR impl₁ adv] = [= true | simulateR impl₂ adv] ∧
        [= false | simulateR impl₁ adv] = [= false | simulateR impl₂ adv] := Iff.rfl

lemma interchangeable_iff_probOutput_true (impl₁ impl₂ : QueryImpl spec ProbComp) :
    impl₁ ≃ₛₒ impl₂ ↔ ∀ adv : Distinguisher spec,
      [= true | simulateR impl₁ adv] = [= true | simulateR impl₂ adv] ∧
        [⊥ | simulateR impl₁ adv] = [⊥ | simulateR impl₂ adv] := by
  refine forall_congr' fun adv => and_congr_right_iff.2 ?_
  have := (probOutput_add_add_probFailure_eq_one (simulateR impl₁ adv)).trans
    (probOutput_add_add_probFailure_eq_one (simulateR impl₂ adv)).symm
  refine fun h => ⟨fun h' => ?_, fun h' => ?_⟩
  · rwa [h, h', add_right_inj (by simp)] at this
  · rwa [h, h', add_left_inj (by simp), add_right_inj (by simp)] at this

lemma interchangeable_iff_probOutput_false (impl₁ impl₂ : QueryImpl spec ProbComp) :
    impl₁ ≃ₛₒ impl₂ ↔ ∀ adv : Distinguisher spec,
      [= false | simulateR impl₁ adv] = [= false | simulateR impl₂ adv] ∧
        [⊥ | simulateR impl₁ adv] = [⊥ | simulateR impl₂ adv] := by
  sorry

lemma interchangeable_iff (impl₁ impl₂ : QueryImpl spec ProbComp) :
    impl₁ ≃ₛₒ impl₂ ↔ ∀ adv : Distinguisher spec,
      [= true | simulateR impl₁ adv] = [= true | simulateR impl₂ adv] ∧
        [= false | simulateR impl₁ adv] = [= false | simulateR impl₂ adv] ∧
          [⊥ | simulateR impl₁ adv] = [⊥ | simulateR impl₂ adv] := by
  sorry

lemma interchangeable_iff_probOutput_bind_guard (impl₁ impl₂ : QueryImpl spec ProbComp) :
    impl₁ ≃ₛₒ impl₂ ↔ ∀ adv : Distinguisher spec,
      [= true | do
        let b ←$ᵗ Bool
        let b' ← simulateR (if b then impl₁ else impl₂) adv
        return (b = b')] = 2⁻¹ := by
  sorry

lemma interchangeable_iff_probOutput_bind_guard' (impl₁ impl₂ : QueryImpl spec ProbComp) :
    impl₁ ≃ₛₒ impl₂ ↔ ∀ adv : Distinguisher spec,
      [= false | do
        let b ←$ᵗ Bool
        let b' ← simulateR (if b then impl₁ else impl₂) adv
        return (b = b')] = 2⁻¹ := by
  sorry

end QueryImpl

noncomputable def Distinguisher.DistinguisherAdvantage (impl₁ impl₂ : QueryImpl spec ProbComp)
    (adv : Distinguisher spec) : ℝ≥0∞ := max
  ([= true | simulateR impl₁ adv] - [= true | simulateR impl₂ adv])
  ([= false | simulateR impl₁ adv] - [= false | simulateR impl₂ adv])

def DistinguisherBound (impl₁ impl₂ : QueryImpl spec ProbComp) (b : ℝ≥0∞) : Prop :=
  ∀ adv : Distinguisher spec, adv.DistinguisherAdvantage impl₁ impl₂ ≤ b

lemma distinguisherBound_iff (impl₁ impl₂ : QueryImpl spec ProbComp) (b : ℝ≥0∞) :
    DistinguisherBound impl₁ impl₂ b ↔ ∀ adv : Distinguisher spec,
      [= true | simulateR impl₁ adv] - [= true | simulateR impl₂ adv] ≤ b ∧
      [= false | simulateR impl₁ adv] - [= false | simulateR impl₂ adv] ≤ b := by
  sorry

lemma DistinguisherBound_zero_iff (impl₁ impl₂ : QueryImpl spec ProbComp) :
    DistinguisherBound impl₁ impl₂ 0 ↔ QueryImpl.Interchangeable impl₁ impl₂ := by
  rw [distinguisherBound_iff, QueryImpl.interchangeable_def]
  simp [tsub_eq_zero_iff_le]
  refine ⟨fun h adv => ?_, fun h adv => by simp [(h adv).1, (h adv).2]⟩
  refine ⟨?_, sorry⟩
  refine le_antisymm (h adv).1 ?_
  rw [probOutput_true_eq_one_sub, probOutput_true_eq_one_sub]

  simp
  sorry

-- def Distinguisher (α _β : Type _) (spec : OracleSpec ι) :=
--   α → OracleComp (unifSpec ++ₒ spec) Bool

-- def Distinguisher.DistinguisherExp (adversary : Distinguisher α β spec)
--     (gen : ProbComp (α × β))
--     (impl₁ impl₂ : α × β → QueryImpl spec ProbComp) :
--     ProbComp Unit := do
--   let b ←$ᵗ Bool
--   let impl := if b then impl₁ else impl₂
--   let x ← gen
--   let b' ← simulateQ (idOracle ++ₛₒ impl x) (adversary x.1)
--   guard (b = b')

-- noncomputable def Distinguisher.advantage (adversary : Distinguisher α β spec)
--     (gen : ProbComp (α × β))
--     (impl₁ impl₂ : α × β → QueryImpl spec ProbComp) :=
--   [= () | adversary.DistinguisherExp gen impl₁ impl₂]
