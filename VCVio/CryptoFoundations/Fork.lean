/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.GenerateSeed
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.Coercions.Append

/-!
# Forking Lemma

-/

open OracleSpec OracleComp Option ENNReal Function

section scratch

variable {ι : Type _} {spec : OracleSpec ι} {α β γ : Type _}

section bind_congr -- TODO: we should have tactics for this kind of thing

variable [spec.FiniteRange]

lemma probFailure_bind_congr (oa : OracleComp spec α)
    {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ}
    (h : ∀ x ∈ oa.support, [⊥ | ob x] = [⊥ | oc x]) : [⊥ | oa >>= ob] = [⊥ | oa >>= oc] := by
  sorry

lemma probFailure_bind_congr' (oa : OracleComp spec α)
    {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ}
    (h : ∀ x, [⊥ | ob x] = [⊥ | oc x]) : [⊥ | oa >>= ob] = [⊥ | oa >>= oc] := by
  sorry

lemma probOutput_bind_congr {oa : OracleComp spec α} {ob₁ ob₂ : α → OracleComp spec β} {y : β}
    (h : ∀ x ∈ oa.support, [= y | ob₁ x] = [= y | ob₂ x]) :
    [= y | oa >>= ob₁] = [= y | oa >>= ob₂] := by
  sorry

lemma probOutput_bind_congr' (oa : OracleComp spec α) {ob₁ ob₂ : α → OracleComp spec β} (y : β)
    (h : ∀ x, [= y | ob₁ x] = [= y | ob₂ x]) :
    [= y | oa >>= ob₁] = [= y | oa >>= ob₂] := by
  sorry

lemma probOutput_bind_mono {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ} {y : β} {z : γ}
    (h : ∀ x ∈ oa.support, [= y | ob x] ≤ [= z | oc x]) :
    [= y | oa >>= ob] ≤ [= z | oa >>= oc] := by
  sorry

lemma probOutput_bind_congr_div_const {oa : OracleComp spec α}
    {ob₁ ob₂ : α → OracleComp spec β} {y : β} {r : ℝ≥0∞}
    (h : ∀ x ∈ oa.support, [= y | ob₁ x] = [= y | ob₂ x] / r) :
    [= y | oa >>= ob₁] = [= y | oa >>= ob₂] / r := by
  sorry

lemma probOutput_bind_congr_eq_add {γ₁ γ₂ : Type _}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β}
      {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ oa.support, [= y | ob x] = [= z₁ | oc₁ x] + [= z₂ | oc₂ x]) :
    [= y | oa >>= ob] = [= z₁ | oa >>= oc₁] + [= z₂ | oa >>= oc₂] := by
  simp [probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ oa.support
  · simp [h x hx, left_distrib]
  · simp [probOutput_eq_zero _ _ hx]

lemma probOutput_bind_congr_le_add {γ₁ γ₂ : Type _}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β}
      {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ oa.support, [= y | ob x] ≤ [= z₁ | oc₁ x] + [= z₂ | oc₂ x]) :
    [= y | oa >>= ob] ≤ [= z₁ | oa >>= oc₁] + [= z₂ | oa >>= oc₂] := by
  sorry

lemma probOutput_bind_congr_add_le {γ₁ γ₂ : Type _}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β}
      {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ oa.support, [= z₁ | oc₁ x] + [= z₂ | oc₂ x] ≤ [= y | ob x]) :
    [= z₁ | oa >>= oc₁] + [= z₂ | oa >>= oc₂] ≤ [= y | oa >>= ob] := by
  sorry

lemma probOutput_bind_congr_le_sub {γ₁ γ₂ : Type _}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β}
      {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ oa.support, [= y | ob x] ≤ [= z₁ | oc₁ x] - [= z₂ | oc₂ x]) :
    [= y | oa >>= ob] ≤ [= z₁ | oa >>= oc₁] - [= z₂ | oa >>= oc₂] := by
  sorry

lemma probOutput_bind_congr_sub_le {γ₁ γ₂ : Type _}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β}
      {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ oa.support, [= z₁ | oc₁ x] - [= z₂ | oc₂ x] ≤ [= y | ob x]) :
    [= z₁ | oa >>= oc₁] - [= z₂ | oa >>= oc₂] ≤ [= y | oa >>= ob] := by
  sorry

end bind_congr

lemma map_ite (oa₁ oa₂ : OracleComp spec α) (f : α → β) (p : Prop) [Decidable p] :
    f <$> (if p then oa₁ else oa₂) = if p then (f <$> oa₁) else (f <$> oa₂) :=
  apply_ite _ _ _ _

lemma probFailure_bind_eq_sum_probFailure [spec.FiniteRange] (oa : OracleComp spec α)
    {ob : α → OracleComp spec β} {σ : Type _} {s : Finset σ}
    {oc : σ → α → OracleComp spec γ} :
    [⊥ | oa >>= ob] = ∑ x ∈ s, [⊥ | oa >>= oc x] := by
  sorry

lemma probOutput_map_eq_probEvent [spec.FiniteRange]
    (oa : OracleComp spec α) (f : α → β) (y : β) :
    [= y | f <$> oa] = [fun x => f x = y | oa] := by
  rw [← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def]

@[simp]
lemma probOutput_prod_mk_fst_map [spec.FiniteRange] (oa : OracleComp spec α) (y : β) (z : α × β) :
    [= z | (·, y) <$> oa] = [= z.1 | oa] * [= z.2 | (pure y : OracleComp spec β)] := by
  sorry

@[simp]
lemma probOutput_prod_mk_snd_map [spec.FiniteRange] (ob : OracleComp spec β) (x : α) (z : α × β) :
    [= z | (x, ·) <$> ob] = [= z.1 | (pure x : OracleComp spec α)] * [= z.2 | ob] := by
  sorry

@[simp]
lemma probOutput_prod_mk_fst_map' [spec.FiniteRange] (oa : OracleComp spec α)
    (f : α → γ) (y : β) (z : γ × β) :
    [= z | (f ·, y) <$> oa] = [= z.1 | f <$> oa] * [= z.2 | (pure y : OracleComp spec β)] := by
  sorry

@[simp]
lemma probOutput_prod_mk_snd_map' [spec.FiniteRange] (ob : OracleComp spec β)
    (f : β → γ) (x : α) (z : α × γ) :
    [= z | (x, f ·) <$> ob] = [= z.1 | (pure x : OracleComp spec α)] * [= z.2 | f <$> ob] := by
  sorry

@[simp]
lemma Option.getM_none {m : Type _ → Type _} {α : Type _} [Alternative m] :
    (Option.getM none : m α) = failure := rfl

@[simp]
lemma Option.getM_some {m : Type _ → Type _} {α : Type _} [Alternative m] (x : α) :
    (Option.getM (some x) : m α) = pure x := rfl

lemma probOutput_bind_ite_failure_eq_tsum [spec.FiniteRange] [DecidableEq β]
    (oa : OracleComp spec α) (f : α → β) (p : α → Prop) [DecidablePred p] (y : β) :
    [= y | oa >>= fun x => if p x then pure (f x) else failure] =
      ∑' x : α, if p x ∧ y = f x then [= x | oa] else 0 := by
  rw [probOutput_bind_eq_tsum]
  simp [probEvent_eq_tsum_ite, ite_and]

end scratch

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [∀ i, SelectableType (spec.range i)] [spec.DecidableEq] [unifSpec ⊂ₒ spec]
  {α β γ : Type}

structure forkInput (spec : OracleSpec ι) (α : Type) where
  /-- The main program to fork execution of -/
  main : OracleComp spec α
  /-- A bound on the number of queries the adversary makes-/
  queryBound : ι → ℕ
  /-- List of oracles that are queried during computation (used to order seed generation). -/
  js : List ι

/-- Version of `fork` that doesn't choose `s` ahead of time.
Should give better concrete bounds. -/
def fork (main : OracleComp spec α)
    (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (α × α) := do
  let seed ← generateSeed spec qb js
  let x₁ ← (simulateQ seededOracle main).run seed
  let s : Fin (qb i + 1) ← (cf x₁).getM
  let u ←$ᵗ spec.range i -- Choose new output for query
  guard ((seed i)[s + 1]? ≠ some u) -- Didn't pick the same output
  let seed' := (seed.takeAtIndex i s).addValue i u
  let x₂ ← (simulateQ seededOracle main).run seed'
  guard (cf x₂ = some s) -- Choose the same index on this run
  return (x₁, x₂)

variable (main : OracleComp spec α) (qb : ι → ℕ)
    (js : List ι) (i : ι) (cf : α → Option (Fin (qb i + 1))) [spec.FiniteRange]

-- open Classical

lemma le_probOutput_fork (s : Fin (qb i + 1)) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.range i))
    let q := qb i + 1
    [= s | cf <$> main] ^ 2 - [= s | cf <$> main] / h
      ≤ [fun (x₁, x₂) => cf x₁ = s ∧ cf x₂ = s | fork main qb js i cf] :=
  let h : ℝ≥0∞ := ↑(Fintype.card (spec.range i))
  let q := qb i + 1
  have : DecidableEq α := Classical.decEq α -- :(
  calc [fun (x₁, x₂) => cf x₁ = s ∧ cf x₂ = s | fork main qb js i cf]
    _ = [= (s, s) | Prod.map cf cf <$> fork main qb js i cf] := by {
        simp [probOutput_map_eq_probEvent, Prod.eq_iff_fst_eq_snd_eq]
      }
    _ = [= (s, s) | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          let u ←$ᵗ spec.range i
          guard ((seed i)[s + 1]? ≠ u)
          let seed' := (seed.takeAtIndex i s).addValue i u
          let x₂ ← (simulateQ seededOracle main).run seed'
          return (cf x₁, cf x₂)] := by {
        simp [fork]
        refine probOutput_bind_congr fun _ _ => ?_
        refine probOutput_bind_congr fun x₁ hx₁ => ?_
        by_cases hcfx₁ : cf x₁ = s
        · simp [hcfx₁]
          refine probOutput_bind_congr fun _ _ => ?_
          refine probOutput_bind_congr fun () _ => ?_
          simp [apply_ite]
          rw [probOutput_bind_ite_failure_eq_tsum, probOutput_map_eq_tsum]
          simp
          refine tsum_congr fun x₂ => ?_
          by_cases hcfx₂ : cf x₂ = s
          · simp [hcfx₂]
          · simp [hcfx₂, Ne.symm hcfx₂]
        · refine (?_ : _ = (0 : ℝ≥0∞)).trans (?_ : (0 : ℝ≥0∞) = _)
          · simp [hcfx₁]
          · simp [hcfx₁]
      }
    _ ≥ [= (s, s) | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          let u ←$ᵗ spec.range i
          let seed' := (seed.takeAtIndex i s).addValue i u
          let x₂ ← (simulateQ seededOracle main).run seed'
          return (cf x₁, cf x₂)] -
        [= (s, s) | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          let u ←$ᵗ spec.range i
          guard ((seed i)[s + 1]? = u)
          let seed' := (seed.takeAtIndex i s).addValue i u
          let x₂ ← (simulateQ seededOracle main).run seed'
          return (cf x₁, cf x₂)] := by {
        rw [ge_iff_le]
        refine probOutput_bind_congr_sub_le fun seed hseed => ?_
        refine probOutput_bind_congr_sub_le fun x₁ hx₁ => ?_
        by_cases hcfx₁ : cf x₁ = s
        · simp [hcfx₁]
          refine probOutput_bind_congr_le_add fun u hu => ?_
          by_cases hu' : (seed i)[(↑(s + 1) : ℕ)]? = some u
          · simp [hu']
          · simp [hu']
        · refine le_of_eq_of_le ?_ zero_le'
          refine tsub_eq_zero_of_le (le_of_eq_of_le ?_ zero_le')
          simp [hcfx₁]
      }
    _ ≥ [= (s, s) | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          let u ←$ᵗ spec.range i
          let seed' := (seed.takeAtIndex i s).addValue i u
          let x₂ ← (simulateQ seededOracle main).run seed'
          return (cf x₁, cf x₂)] -
        [= s | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          let u ←$ᵗ spec.range i
          guard ((seed i)[s + 1]? = u)
          return (cf x₁)] := by {
        refine tsub_le_tsub le_rfl ?_
        refine probOutput_bind_mono fun seed hseed => ?_
        refine probOutput_bind_mono fun x₁ hx₁ => ?_
        refine probOutput_bind_mono fun u hu => ?_
        refine probOutput_bind_mono fun () _ => ?_
        by_cases hcfx₁ : some s = cf x₁
        · simp [hcfx₁]
        · simp [hcfx₁]
      }
    _ = [= (s, s) | do
          let shared_seed ← liftM (generateSeed spec (Function.update qb i q) js)
          let x₁ ← (simulateQ seededOracle main).run shared_seed
          let x₂ ← (simulateQ seededOracle main).run shared_seed
          return (cf x₁, cf x₂)] -
        [= s | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          return (cf x₁)] / h := by {
        congr 1
        ·
          sorry
        · refine probOutput_bind_congr_div_const fun seed hseed => ?_
          have : (↑(s + 1) : ℕ) < (seed i).length := sorry
          let u : spec.range i := ((seed i)[↑(s + 1)])
          simp [probOutput_bind_eq_tsum, probOutput_map_eq_tsum, div_eq_mul_inv,
            ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun x => ?_
          refine (tsum_eq_single ((seed i)[(↑(s + 1) : ℕ)]) ?_).trans ?_
          · intro u' hu'
            rw [List.getElem?_eq_getElem this]
            simp [hu'.symm]
          · simp [h]
      }
    _ ≥ [= s | cf <$> main] ^ 2 - [= s | cf <$> main] / h := by {
        refine tsub_le_tsub ?_ ?_
        · sorry
        · sorry
      }

theorem probFailure_fork_le :
    let acc : ℝ≥0∞ := 1 - [= none | cf <$> main]
    let h : ℝ≥0∞ := Fintype.card (spec.range i)
    let q := qb i + 1
    [⊥ | fork main qb js i cf] ≤ 1 - acc * (acc / q - h⁻¹) := by
  let acc : ℝ≥0∞ := 1 - [= none | cf <$> main]
  let h : ℝ≥0∞ := Fintype.card (spec.range i)
  let q := qb i + 1
  calc [⊥ | fork main qb js i cf]
    _ = 1 - ∑ s, [= (s, s) | Prod.map cf cf <$> fork main qb js i cf] := by
      sorry
    _ ≤ 1 - ∑ s, ([= s | cf <$> main] ^ 2 - [= s | cf <$> main] / h) := by
      sorry
    _ = 1 - (∑ s, [= s | cf <$> main] ^ 2) - (∑ s, [= s | cf <$> main] / h) := by
      sorry
    _ ≤ 1 - (∑ s, [= s | cf <$> main]) ^ 2 / q - (∑ s, [= s | cf <$> main]) / h := by
      sorry
    _ ≤ 1 - acc ^ 2 / q + acc / h := by
      sorry
    _ = 1 - acc * (acc / q - h⁻¹) := by
      sorry

theorem exists_log_of_mem_support_fork (x₁ x₂ : α)
    (h : (x₁, x₂) ∈ (fork main qb js i cf).support) :
      ∃ s, cf x₁ = some s ∧ cf x₂ = some s ∧
      ∃ log₁ : QueryLog spec, ∃ hcf₁ : ↑s < log₁.countQ i,
      ∃ log₂ : QueryLog spec, ∃ hcf₁ : ↑s < log₂.countQ i,
      (log₁.getQ i)[s].1 = (log₂.getQ i)[s].1 ∧
      (log₁.getQ i)[s].2 ≠ (log₂.getQ i)[s].2 ∧
      (x₁, log₁) ∈ (simulateQ loggingOracle main).run.support ∧
      (x₂, log₂) ∈ (simulateQ loggingOracle main).run.support :=
  sorry

end OracleComp
