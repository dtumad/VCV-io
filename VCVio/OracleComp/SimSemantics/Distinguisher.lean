/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Append
import VCVio.CryptoFoundations.Asymptotics.PolyTimeOC

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
def Distinguisher (spec : OracleSpec ι) :
    Type _ :=
  OracleComp (unifSpec ++ₒ spec) Bool

-- structure Distinguisher' (spec : ℕ → OracleSpec ι) where
--   main (sp : ℕ) : OracleComp (spec sp) Bool
--   main_polyTime : OracleComp.PolyTime main

namespace QueryImpl

/-- Two `QueryImpl` are interchangeable if they always induce the same chance of a distinguisher
returning `true` and `false` with those implementations (see `Interchangeable_iff`).
We include both conditions to factor in the chance of `adv` resulting in `failure`. -/
def Interchangeable (impl₁ impl₂ : QueryImpl spec ProbComp) : Prop :=
  ∀ adv : Distinguisher spec,
    [= true | simulateR impl₁ adv] =
      [= true | simulateR impl₂ adv]

infixr:25 " ≃ₛₒ " => Interchangeable

instance : IsEquiv (QueryImpl spec ProbComp) Interchangeable where
  refl _ _ := rfl
  symm _ _ h adv := (h adv).symm
  trans _ _ _ h₁ h₂ adv := (h₁ adv).trans (h₂ adv)

lemma Interchangeable_iff (impl₁ impl₂ : QueryImpl spec ProbComp) :
    impl₁ ≃ₛₒ impl₂ ↔ ∀ adv : Distinguisher spec,
    [= true | simulateR impl₁ adv] = [= true | simulateR impl₂ adv] ∧
      [= false | simulateR impl₁ adv] = [= false | simulateR impl₂ adv] := by
  refine ⟨fun h adv => ⟨h adv, ?_⟩, fun h adv => (h adv).1⟩
  simpa [simulateR] using h (Bool.not <$> adv)

lemma Interchangeable_iff_probOutput_true (impl₁ impl₂ : QueryImpl spec ProbComp) :
    impl₁ ≃ₛₒ impl₂ ↔ ∀ adv : Distinguisher spec,
    [= true | simulateR impl₁ adv] = [= true | simulateR impl₂ adv] := by rfl

lemma Interchangeable_iff_probOutput_false (impl₁ impl₂ : QueryImpl spec ProbComp) :
    impl₁ ≃ₛₒ impl₂ ↔ ∀ adv : Distinguisher spec,
    [= false | simulateR impl₁ adv] = [= false | simulateR impl₂ adv] := by
  rw [Interchangeable_iff_probOutput_true]
  refine ⟨fun h adv => by simpa [simulateR] using h (Bool.not <$> adv),
    fun h adv => by simpa [simulateR] using h (Bool.not <$> adv)⟩

lemma interchangeable_iff_probOutput_true (impl₁ impl₂ : QueryImpl spec ProbComp) :
    impl₁ ≃ₛₒ impl₂ ↔ ∀ adv : Distinguisher spec,
      [= true | simulateR impl₁ adv] = [= true | simulateR impl₂ adv] ∧
        [⊥ | simulateR impl₁ adv] = [⊥ | simulateR impl₂ adv] := by
  refine (Interchangeable_iff _ _).trans ?_
  refine forall_congr' fun adv => and_congr_right_iff.2 ?_
  have := (probOutput_bool_add_probFailure_eq_one (simulateR impl₁ adv) true).trans
    (probOutput_bool_add_probFailure_eq_one (simulateR impl₂ adv) true).symm
  simp only [Bool.not_true] at this
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

-- noncomputable def Distinguisher.DistinguisherAdvantage' (impl₁ impl₂ : QueryImpl spec ProbComp)
--     (adv : Distinguisher spec) : ℝ≥0∞ := [= () | do
--       let b ←$ᵗ Bool
--       let b' ← simulateR (if b then impl₁ else impl₂) adv
--       guard (b = b')]

noncomputable def Distinguisher.DistinguisherAdvantage (impl₁ impl₂ : QueryImpl spec ProbComp)
    (adv : Distinguisher spec) : ℝ≥0∞ := --max
  ([= true | simulateR impl₁ adv] - [= true | simulateR impl₂ adv])
  -- ([= true | simulateR impl₂ adv] - [= true | simulateR impl₁ adv])
  -- |[= true | simulateR impl₁ adv].toReal - [= true | simulateR impl₂ adv].toReal|.toENNReal

open Distinguisher

def DistinguisherBound (impl₁ impl₂ : QueryImpl spec ProbComp) (b : ℝ≥0∞) : Prop :=
  ∀ adv : Distinguisher spec, DistinguisherAdvantage impl₁ impl₂ adv ≤ b

/-- Adversaries have no incentive to fail since it reduces their success chance.
Therefore we can quantify over only adversaries that don't fail to prove distinguisher bounds. -/
lemma DistinguisherBound_iff_forall_noFailure (impl₁ impl₂ : QueryImpl spec ProbComp) (b : ℝ≥0∞) :
    DistinguisherBound impl₁ impl₂ b ↔ ∀ adv : Distinguisher spec,
      neverFails adv → DistinguisherAdvantage impl₁ impl₂ adv ≤ b := by
  sorry

/-- No adversary can distinguish an implementation from itself. -/
lemma DistinguisherBound.refl (impl : QueryImpl spec ProbComp) :
    DistinguisherBound impl impl 0 := by
  simp [DistinguisherBound, DistinguisherAdvantage]

/-- Distinguishing two computations in reverse order doesn't change the bound.
Note that the adversaries acheiving the bound will be different in each case,
but when we quantify over them all this doesn't make a difference. -/
lemma DistinguisherBound.symm (impl₁ impl₂ : QueryImpl spec ProbComp) (b : ℝ≥0∞) :
    DistinguisherBound impl₁ impl₂ b ↔ DistinguisherBound impl₂ impl₁ b := by
  refine ⟨fun h adv => ?_, sorry⟩

  specialize h (Bool.not <$> adv)
  simp only [DistinguisherAdvantage, simulateR, simulateQ_map] at h
  simp only [DistinguisherAdvantage, simulateR]

  simp only [probOutput_map_not, Bool.not_true,
    probOutput_bool_eq_one_sub _ false, Bool.not_false] at h
  refine le_trans ?_ h
  rw [← ENNReal.toReal_le_toReal]
  · rw [ENNReal.toReal_sub_of_le]
    ·
      sorry
    ·
      sorry

    sorry
  ·
    sorry
  ·
    sorry

lemma DistinguisherBound.trans (impl₁ impl₂ impl₃ : QueryImpl spec ProbComp)
    (b b' : ℝ≥0∞) (h : DistinguisherBound impl₁ impl₂ b)
    (h' : DistinguisherBound impl₂ impl₃ b') :
    DistinguisherBound impl₁ impl₃ (b + b') := by
  sorry



lemma distinguisherBound_iff_probOutput_true (impl₁ impl₂ : QueryImpl spec ProbComp) (b : ℝ≥0∞) :
    DistinguisherBound impl₁ impl₂ b ↔ ∀ adv : Distinguisher spec,
      [= true | simulateR impl₁ adv] - [= true | simulateR impl₂ adv] ≤ b := by
  rfl

lemma distinguisherBound_iff_probOutput_true' (impl₁ impl₂ : QueryImpl spec ProbComp) (b : ℝ≥0∞) :
    DistinguisherBound impl₁ impl₂ b ↔ ∀ adv : Distinguisher spec,
      [= true | simulateR impl₂ adv] - [= true | simulateR impl₁ adv] ≤ b := by

  sorry

lemma distinguisherBound_iff_probOutput_false (impl₁ impl₂ : QueryImpl spec ProbComp) (b : ℝ≥0∞) :
    DistinguisherBound impl₁ impl₂ b ↔ ∀ adv : Distinguisher spec,
      [= false | simulateR impl₁ adv] - [= false | simulateR impl₂ adv] ≤ b := by

  sorry

lemma distinguisherBound_iff_probOutput_false' (impl₁ impl₂ : QueryImpl spec ProbComp) (b : ℝ≥0∞) :
    DistinguisherBound impl₁ impl₂ b ↔ ∀ adv : Distinguisher spec,
      [= false | simulateR impl₂ adv] - [= false | simulateR impl₁ adv] ≤ b := by
  sorry



lemma DistinguisherBound_of_reduction {ι' : Type _} {rspec : OracleSpec ι'}
    {impl₁ impl₂ : QueryImpl spec ProbComp}
    {red_impl₁ red_impl₂ : QueryImpl rspec ProbComp}
    {b r : ℝ≥0∞}
    (hr : DistinguisherBound red_impl₁ red_impl₂ r)
    (reduction : Distinguisher spec → Distinguisher rspec)
    (h : ∀ adv : Distinguisher spec,
      Distinguisher.DistinguisherAdvantage impl₁ impl₂ adv > b →
        Distinguisher.DistinguisherAdvantage red_impl₁ red_impl₂ (reduction adv) > r) :
    DistinguisherBound impl₁ impl₂ b :=
  sorry



lemma DistinguisherBound_append_right (impl₁ impl₂ : QueryImpl spec ProbComp)
    (b : ℝ≥0∞) {τ : Type _} {spec' : OracleSpec τ} (implᵣ : QueryImpl spec' ProbComp) :
    DistinguisherBound (impl₁ ++ₛₒ implᵣ) (impl₂ ++ₛₒ implᵣ) b ↔
      DistinguisherBound impl₁ impl₂ b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · intro adv
    let adv' : Distinguisher (spec ++ₒ spec') := liftComp adv _
    specialize h (liftComp adv _)
    unfold DistinguisherAdvantage
    unfold DistinguisherAdvantage at h
    unfold simulateR at *
    simpa using h
  · intro adv
    unfold DistinguisherBound at h
    unfold DistinguisherAdvantage at *
    unfold simulateR at *

    let adv' : Distinguisher spec := simulateQ ((idOracle unifSpec) ++ₛₒ ((idOracle spec) ++ₛₒ implᵣ)) adv
    specialize h adv'
    unfold adv' at h
    convert h
    · simp
      rw [← QueryImpl.simulateQ_compose]
      congr 1
      refine QueryImpl.ext' fun
        | query (.inl i) t => ?_
        | query (.inr (.inl i)) t => ?_
        | query (.inr (.inr i)) t => ?_
      · simp
      · simp
      · simp
    · simp
      rw [← QueryImpl.simulateQ_compose]
      congr 1
      refine QueryImpl.ext' fun
        | query (.inl i) t => ?_
        | query (.inr (.inl i)) t => ?_
        | query (.inr (.inr i)) t => ?_
      · simp
      · simp
      · simp



lemma DistinguisherBound_iff (impl₁ impl₂ : QueryImpl spec ProbComp) (b : ℝ≥0∞) :
    DistinguisherBound impl₁ impl₂ b ↔ ∀ adv : Distinguisher spec,
      [= true | simulateR impl₁ adv] - [= true | simulateR impl₂ adv] ≤ b ∧
      [= false | simulateR impl₁ adv] - [= false | simulateR impl₂ adv] ≤ b ∧
      [= true | simulateR impl₂ adv] - [= true | simulateR impl₁ adv] ≤ b ∧
      [= false | simulateR impl₂ adv] - [= false | simulateR impl₁ adv] ≤ b := by
  sorry
  -- refine ⟨fun h adv => ?_, fun h adv => ?_⟩
  -- · refine ⟨h adv, ⟨?_, ⟨?_, ?_⟩⟩⟩

  --   · specialize h (Bool.not <$> adv)
  --     simpa [simulateR] using h
  --   ·
  --     specialize h (Bool.not <$> adv)

  --     simp [simulateR] at *

  --     sorry
  --   sorry
  -- · refine (h adv).1


-- def DistinguisherBound (impl₁ impl₂ : QueryImpl spec ProbComp) (b : ℝ≥0∞) : Prop :=
--   ∀ adv : Distinguisher spec, adv.DistinguisherAdvantage impl₁ impl₂ ≤ b

-- lemma distinguisherBound_iff (impl₁ impl₂ : QueryImpl spec ProbComp) (b : ℝ≥0∞) :
--     DistinguisherBound impl₁ impl₂ b ↔ ∀ adv : Distinguisher spec,
--       [= true | simulateR impl₁ adv] - [= true | simulateR impl₂ adv] ≤ b ∧
--       [= false | simulateR impl₁ adv] - [= false | simulateR impl₂ adv] ≤ b := by
--   rw [DistinguisherBound]
--   apply forall_congr' fun adv => ?_
--   rw [Distinguisher.DistinguisherAdvantage]
--   simp only [sup_le_iff, tsub_le_iff_right]
--   sorry


-- lemma DistinguisherBound_zero_iff (impl₁ impl₂ : QueryImpl spec ProbComp) :
--     DistinguisherBound impl₁ impl₂ 0 ↔ QueryImpl.Interchangeable impl₁ impl₂ := by
--   rw [distinguisherBound_iff, QueryImpl.interchangeable_iff]
--   simp [tsub_eq_zero_iff_le]
--   refine ⟨fun h adv => ?_, fun h adv => by simp [(h adv).1, (h adv).2]⟩
--   refine ⟨?_, sorry⟩
--   refine le_antisymm (h adv).1 ?_
--   have := (h adv).2
--   -- rw [probOutput_true_eq_one_sub, probOutput_true_eq_one_sub]

--   sorry

-- /-- The oracle that compares its input to a random value can't be distinguished from one that
-- always fails with probability more than the chance of them returning the same value. -/
-- lemma distinguisherBound_predict_inv_card {τ υ : Type _}
--     [SelectableType τ] [Fintype τ] [DecidableEq τ] (b : Bool) :
--     let predict : QueryImpl (τ →ₒ Bool) ProbComp :=
--       QueryImpl.ofFn fun t => do return ((← $ᵗ τ) = t)
--     let give_up : QueryImpl (τ →ₒ Bool) ProbComp :=
--       QueryImpl.ofFn fun t => do return false
--     DistinguisherBound predict give_up (Fintype.card τ)⁻¹ := by
--   sorry

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
