/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ToMathlib.ProbabilityTheory.Coupling
import Mathlib.Probability.ProbabilityMassFunction.Monad
import ToMathlib.General


/-!
# Denotational Semantics for Output Distributions

This file defines a typeclass for monads that can be canonically embedded in the `PMF` monad.
We require this embedding respect the basic monad laws.

We also define a number of specific cases:

* `PrPr[= x | mx]` / `probOutput mx x` for odds of `mx` returning `x`
* `Pr[p | mx]` / `probEvent mx p` for odds of `mx`'s result satisfying `p`
* `Pr[e | x ← mx]` where `x` is free in the expression `e`
* `PrPr[⊥ | mx]` / `probFailure mx` for odds of `mx` resulting in failure

For the last case, we assume `mx` has an `OptionT` transformer to represent the failure.
In future it may be nice to generalize to any `AlternativeMonad` using an additional typeclass
  (note that it can't extend the existing one as it outputs in an `SPMF`).
-/

open ENNReal

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

class HasEvalDist (m : Type u → Type v) [Monad m] where
  evalDist {α : Type u} (mx : m α) : SPMF α
  evalDist_pure {α : Type u} (x : α) : evalDist (pure x : m α) = pure x
  evalDist_bind {α β : Type u} (mx : m α) (my : α → m β) :
    evalDist (mx >>= my) = evalDist mx >>= evalDist ∘ my

export HasEvalDist (evalDist evalDist_pure evalDist_bind)
attribute [simp] evalDist_pure evalDist_bind

variable [HasEvalDist m]

/-- Probability that a computation `mx` returns the value `x`. -/
def probOutput [HasEvalDist m] (mx : m α) (x : α) : ℝ≥0∞ := (evalDist mx).run (some x)

/-- Probability that a computation `mx` outputs a value satisfying `p`. -/
noncomputable def probEvent [HasEvalDist m] (mx : m α) (p : α → Prop) : ℝ≥0∞ :=
  (evalDist mx).run.toOuterMeasure (some '' {x | p x})

/-- Probability that a compuutation `mx` will fail to return a value. -/
def probFailure [HasEvalDist m] (mx : m α) : ℝ≥0∞ := evalDist mx none

notation "Pr[=" x "|" mx "]" => probOutput mx x
notation "Pr[" p "|" mx "]" => probEvent mx p
notation "Pr[⊥" "|" mx "]" => probFailure mx

syntax (name := probEventBinding)
  "Pr[" term " | " ident " ← " term "]" : term

macro_rules | `(Pr[$cond:term | $var:ident ← $src:term]) => `(Pr[fun $var => $cond | $src])

example {m : Type → Type} [Monad m] [HasEvalDist m] (mx : m ℕ) : Unit :=
  let _ := Pr[= 10 | mx]
  let _ := Pr[fun x => x^2 + x < 10 | mx]
  let _ := Pr[x^2 + x < 10 | x ← mx]
  ()

lemma probOutput_def (mx : m α) (x : α) : Pr[= x | mx] = (evalDist mx).run (some x) := rfl

lemma probEvent_def (mx : m α) (p : α → Prop) :
    Pr[p | mx] = (evalDist mx).run.toOuterMeasure (some '' {x | p x}) := rfl

lemma probFailure_def (mx : m α) : Pr[⊥ | mx] = evalDist mx none := rfl

@[simp] lemma evalDist_comp_pure : evalDist ∘ (pure : α → m α) = pure := by
  simp [funext_iff, Function.comp_apply, evalDist_pure]

@[simp] lemma evalDist_comp_pure' (f : α → β) : evalDist ∘ (pure : β → m β) ∘ f = pure ∘ f := by
  simp only [← Function.comp_assoc, evalDist_comp_pure]

@[simp] lemma probOutput_pure [DecidableEq α] (x y : α) :
    Pr[= x | (pure y : m α)] = if x = y then 1 else 0 := by simp [probOutput_def]

@[simp] lemma evalDist_map [LawfulMonad m] (mx : m α) (f : α → β) :
    evalDist (f <$> mx) = f <$> (evalDist mx) := by
  simp only [map_eq_bind_pure_comp, evalDist_bind, evalDist_comp_pure']

@[simp] lemma evalDist_comp_map [LawfulMonad m] (mx : m α) :
    evalDist ∘ (fun f => f <$> mx) = fun f : (α → β) => f <$> evalDist mx := by simp [funext_iff]

@[simp] lemma evalDist_seq [LawfulMonad m] (mf : m (α → β)) (mx : m α) :
    evalDist (mf <*> mx) = evalDist mf <*> evalDist mx := by simp [seq_eq_bind_map]

@[simp] lemma evalDist_ite (p : Prop) [Decidable p] (mx mx' : m α) :
    evalDist (if p then mx else mx') = if p then evalDist mx else evalDist mx' := by
  by_cases hp : p <;> simp [hp]

section sums

lemma probEvent_eq_tsum_indicator (mx : m α) (p : α → Prop) :
    Pr[p | mx] = ∑' x : α, {x | p x}.indicator (Pr[= · | mx]) x := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, Set.indicator_image (Option.some_injective _),
    tsum_option _ ENNReal.summable, probOutput_def, Function.comp_def]

/-- More explicit form of `probEvent_eq_tsum_indicator` when the predicate `p` is decidable. -/
lemma probEvent_eq_tsum_ite (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = ∑' x : α, if p x then Pr[= x | mx] else 0 := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, tsum_option _ ENNReal.summable,
    Set.indicator, probOutput_def]

end sums

section bounds

variable {mx : m α} {mxe : OptionT m α} {x : α} {p : α → Prop}

@[simp] lemma probOutput_le_one : Pr[= x | mx] ≤ 1 := PMF.coe_le_one (evalDist mx) x
@[simp] lemma probOutput_ne_top : Pr[= x | mx] ≠ ∞ := PMF.apply_ne_top (evalDist mx) x
@[simp] lemma probOutput_lt_top : Pr[= x | mx] < ∞ := PMF.apply_lt_top (evalDist mx) x
@[simp] lemma not_one_lt_probOutput : ¬ 1 < Pr[= x | mx] := not_lt.2 probOutput_le_one

-- @[simp] lemma tsum_probOutput_le_one : ∑' x : α, Pr[= x | mx] ≤ 1 :=
--   le_of_le_of_eq (le_add_self) (probFailure_add_tsum_probOutput mx)
-- @[simp] lemma tsum_probOutput_ne_top : ∑' x : α, Pr[= x | mx] ≠ ⊤ :=
--   ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one

-- @[simp] lemma probEvent_ne_top : Pr[p | mx] ≠ ∞ := ne_top_of_le_ne_top one_ne_top probEvent_le_one
-- @[simp] lemma probEvent_lt_top : Pr[p | mx] < ∞ := lt_top_iff_ne_top.2 probEvent_ne_top
-- @[simp] lemma not_one_lt_probEvent : ¬ 1 < Pr[p | mx] := not_lt.2 probEvent_le_one

-- @[simp] lemma probEvent_le_one : Pr[p | mx] ≤ 1 := by
--   rw [probEvent_def, PMF.toOuterMeasure_apply]
--   refine le_of_le_of_eq (ENNReal.tsum_le_tsum ?_) (mx.evalDist.tsum_coe)
--   exact Set.indicator_le_self (some '' {x | p x}) _

-- @[simp] lemma probFailure_le_one : Pr[⊥ | mx] ≤ 1 := PMF.coe_le_one (evalDist mx) none
-- @[simp] lemma probFailure_ne_top : Pr[⊥ | mx] ≠ ∞ := PMF.apply_ne_top (evalDist mx) none
-- @[simp] lemma probFailure_lt_top : Pr[⊥ | mx] < ∞ := PMF.apply_lt_top (evalDist mx) none
-- @[simp] lemma not_one_lt_probFailure : ¬ 1 < Pr[⊥ | mx] := not_lt.2 probFailure_le_one
-- @[simp] lemma probFailure_eq_zero [HasEvalDist.NoFailure m] (mx : m α) :
--     Pr[⊥ | mx] = 0 := HasEvalDist.NoFailure.evalDist_apply_none_eq_zero mx

-- @[simp] lemma one_le_probOutput_iff : 1 ≤ Pr[= x | mx] ↔ Pr[= x | mx] = 1 := by
--   simp only [le_iff_eq_or_lt, not_one_lt_probOutput, or_false, eq_comm]
-- @[simp] lemma one_le_probEvent_iff : 1 ≤ [p | mx] ↔ [p | mx] = 1 := by
--   simp only [le_iff_eq_or_lt, not_one_lt_probEvent, or_false, eq_comm]
-- @[simp] lemma one_le_probFailure_iff : 1 ≤ Pr[⊥ | mx] ↔ Pr[⊥ | mx] = 1 := by
--   simp only [le_iff_eq_or_lt, not_one_lt_probFailure, or_false, eq_comm]

end bounds

namespace PMF

noncomputable instance hasEvalDist : HasEvalDist PMF where
  evalDist p := OptionT.mk p
  evalDist_pure _ := by simp; rfl
  evalDist_bind x y := by
    simp [Function.comp_def, OptionT.mk, bind_assoc]
    sorry

variable (p : PMF α) (x : α)

@[simp] lemma evalDist_eq : evalDist p = liftM p := rfl

@[simp] lemma probOutput_eq : probOutput p = p := by
  refine funext fun x => ?_
  simp only [probOutput_def, evalDist_eq, monad_pure_eq_pure, monad_bind_eq_bind, OptionT.run_mk,
    pure_apply, Option.some.injEq, mul_ite, mul_one, mul_zero]
  simp

@[simp] lemma probEvent_eq : probEvent p = p.toOuterMeasure := by
  refine funext fun x => ?_
  simp [probEvent_def, monad_map_eq_map]
  rw [Set.preimage_image_eq]
  rfl
  exact Option.some_injective α

end PMF
