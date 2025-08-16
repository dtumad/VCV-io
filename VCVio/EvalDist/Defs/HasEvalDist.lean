/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, František Silváši
-/
import VCVio.EvalDist.Defs.SPMF
import VCVio.EvalDist.Defs.HasSupportM

/-!
# Denotational Semantics for Output Distributions

This file defines a typeclass for monads that can be canonically embedded in the `SPMF` monad.
We require this embedding respect the basic monad laws.

We also define a number of specific cases:

* `Pr[= x | mx]` / `probOutput mx x` for odds of `mx` returning `x`
* `Pr[p | mx]` / `probEvent mx p` for odds of `mx`'s result satisfying `p`
* `Pr[e | x ← mx]` where `x` is free in the expression `e`
* `Pr{x ← mx}[e]` where `x` is free in the expression `e`
* `Pr[⊥ | mx]` / `probFailure mx` for odds of `mx` resulting in failure

For the last case, we assume `mx` has an `OptionT` transformer to represent the failure.
In future it may be nice to generalize to any `AlternativeMonad` using an additional typeclass
  (note that it can't extend the existing one as it outputs in an `SPMF`).
-/

open ENNReal

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

/-- The monad `m` has a well-behaved embedding into the `SPMF` monad.
TODO: modify this to extend `MonadHom` to get some lemmas for free. -/
class HasEvalDist (m : Type u → Type v) [Monad m]
    extends HasSupportM m where
  evalDist : m →ᵐ SPMF
  support_eq {α : Type u} (mx : m α) : support mx = {x | evalDist mx x ≠ 0}

export HasEvalDist (evalDist)

/-- Probability that a computation `mx` returns the value `x`. -/
def probOutput [HasEvalDist m] (mx : m α) (x : α) : ℝ≥0∞ := evalDist mx x

/-- Probability that a computation `mx` outputs a value satisfying `p`. -/
noncomputable def probEvent [HasEvalDist m] (mx : m α) (p : α → Prop) : ℝ≥0∞ :=
  (evalDist mx).run.toOuterMeasure (some '' {x | p x})

/-- Probability that a compuutation `mx` will fail to return a value. -/
def probFailure [HasEvalDist m] (mx : m α) : ℝ≥0∞ := (evalDist mx).run none

/-- Probability that a computation returns a particular output. -/
notation "Pr[=" x "|" mx "]" => probOutput mx x

/-- Probability that a computation returns a value satisfying a predicate. -/
notation "Pr[" p "|" mx "]" => probEvent mx p

/-- Probability that a computation fails to return a value. -/
notation "Pr[⊥" "|" mx "]" => probFailure mx

/-- Probability that a computation returns a value satisfying a predicate. -/
syntax (name := probEventBinding1)
  "Pr[" term " | " ident " ← " term "]" : term

macro_rules (kind := probEventBinding1)
  | `(Pr[$cond:term | $var:ident ← $src:term]) => `(Pr[fun $var => $cond | $src])

/-- Probability that a computation returns a value satisfying a predicate. -/
syntax (name := probEventBinding2) "Pr{" doSeq "}[" term "]" : term

macro_rules (kind := probEventBinding2)
  -- `doSeqBracketed`
  | `(Pr{{$items*}}[$t]) => `(probOutput (do $items:doSeqItem* return $t:term) True)
  -- `doSeqIndent`
  | `(Pr{$items*}[$t]) => `(probOutput (do $items:doSeqItem* return $t:term) True)

/-- Test for all the different probability notations. -/
example {m : Type → Type u} [Monad m] [HasEvalDist m] (mx : m ℕ) : Unit :=
  let _ := Pr[= 10 | mx]
  let _ := Pr[fun x => x^2 + x < 10 | mx]
  let _ := Pr[x^2 + x < 10 | x ← mx]
  let _ := Pr{let x ← mx}[x = 10]
  let _ := Pr[⊥ | mx]
  ()

variable [HasEvalDist m]

lemma probOutput_def (mx : m α) (x : α) : Pr[= x | mx] = (evalDist mx).run (some x) := rfl

lemma probEvent_def (mx : m α) (p : α → Prop) :
    Pr[p | mx] = (evalDist mx).run.toOuterMeasure (some '' {x | p x}) := rfl

lemma probFailure_def (mx : m α) : Pr[⊥ | mx] = (evalDist mx).run none := rfl

@[simp] lemma evalDist_pure {α : Type u} (x : α) : evalDist (pure x : m α) = pure x :=
  MonadHom.toFun_pure' _ x

@[simp] lemma evalDist_bind {α β : Type u} (mx : m α) (my : α → m β) :
    evalDist (mx >>= my) = evalDist mx >>= fun x => evalDist (my x) :=
  MonadHom.toFun_bind' _ mx my

@[simp] lemma evalDist_comp_pure : evalDist.toFun ∘ (pure : α → m α) = pure := by
  simp [funext_iff, Function.comp_apply]

@[simp] lemma evalDist_comp_pure' (f : α → β) :
    evalDist.toFun ∘ (pure : β → m β) ∘ f = pure ∘ f := by
  simp only [← Function.comp_assoc, evalDist_comp_pure]

@[simp] lemma probOutput_pure [DecidableEq α] (x y : α) :
    Pr[= x | (pure y : m α)] = if x = y then 1 else 0 := by simp [probOutput_def]

lemma probOutput_pure_eq_indicator (x y : α) :
    Pr[= x | (pure y : m α)] = Set.indicator (M := ℝ≥0∞) {y} (Function.const _ 1) x := by
  simp only [probOutput_def, evalDist_pure, OptionT.run_pure, PMF.monad_pure_eq_pure,
    PMF.pure_apply, Option.some.injEq, Set.indicator, Set.mem_singleton_iff, Function.const_apply]
  rw [Option.some_inj]
  rfl

@[simp] lemma evalDist_map [LawfulMonad m] (mx : m α) (f : α → β) :
    evalDist (f <$> mx) = f <$> (evalDist mx) := by
  simp [map_eq_bind_pure_comp]

@[simp] lemma evalDist_comp_map [LawfulMonad m] (mx : m α) : evalDist.toFun ∘ (fun f => f <$> mx) =
    fun f : (α → β) => f <$> evalDist mx := by simp [funext_iff]

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

lemma probEvent_eq_tsum_ite (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = ∑' x : α, if p x then Pr[= x | mx] else 0 := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, tsum_option _ ENNReal.summable,
    Set.indicator, probOutput_def]

@[simp] lemma probFailure_add_tsum_probOutput (oa : m α) :
    Pr[⊥ | oa] + ∑' x, Pr[= x | oa] = 1 :=
  (tsum_option _ ENNReal.summable).symm.trans (evalDist oa).tsum_coe

@[simp] lemma tsum_probOutput_add_probFailure (oa : m α) :
    ∑' x, Pr[= x | oa] + Pr[⊥ | oa] = 1 :=
  by rw [add_comm, probFailure_add_tsum_probOutput]

end sums

section bounds

variable {mx : m α} {mxe : OptionT m α} {x : α} {p : α → Prop}

@[simp] lemma probOutput_le_one : Pr[= x | mx] ≤ 1 := PMF.coe_le_one (evalDist mx) x
@[simp] lemma probOutput_ne_top : Pr[= x | mx] ≠ ∞ := PMF.apply_ne_top (evalDist mx) x
@[simp] lemma probOutput_lt_top : Pr[= x | mx] < ∞ := PMF.apply_lt_top (evalDist mx) x
@[simp] lemma not_one_lt_probOutput : ¬ 1 < Pr[= x | mx] := not_lt.2 probOutput_le_one

@[simp] lemma tsum_probOutput_le_one : ∑' x : α, Pr[= x | mx] ≤ 1 :=
  le_of_le_of_eq (le_add_self) (probFailure_add_tsum_probOutput mx)
@[simp] lemma tsum_probOutput_ne_top : ∑' x : α, Pr[= x | mx] ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one

@[simp] lemma probEvent_le_one : Pr[p | mx] ≤ 1 := by
  rw [probEvent_def, PMF.toOuterMeasure_apply]
  refine le_of_le_of_eq (ENNReal.tsum_le_tsum ?_) ((evalDist mx).tsum_coe)
  exact Set.indicator_le_self (some '' {x | p x}) _

@[simp] lemma probEvent_ne_top : Pr[p | mx] ≠ ∞ := ne_top_of_le_ne_top one_ne_top probEvent_le_one
@[simp] lemma probEvent_lt_top : Pr[p | mx] < ∞ := lt_top_iff_ne_top.2 probEvent_ne_top
@[simp] lemma not_one_lt_probEvent : ¬ 1 < Pr[p | mx] := not_lt.2 probEvent_le_one

@[simp] lemma probFailure_le_one : Pr[⊥ | mx] ≤ 1 := PMF.coe_le_one (evalDist mx) none
@[simp] lemma probFailure_ne_top : Pr[⊥ | mx] ≠ ∞ := PMF.apply_ne_top (evalDist mx) none
@[simp] lemma probFailure_lt_top : Pr[⊥ | mx] < ∞ := PMF.apply_lt_top (evalDist mx) none
@[simp] lemma not_one_lt_probFailure : ¬ 1 < Pr[⊥ | mx] := not_lt.2 probFailure_le_one

@[simp] lemma one_le_probOutput_iff : 1 ≤ Pr[= x | mx] ↔ Pr[= x | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probOutput, or_false, eq_comm]
@[simp] lemma one_le_probEvent_iff : 1 ≤ Pr[p | mx] ↔ Pr[p | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probEvent, or_false, eq_comm]
@[simp] lemma one_le_probFailure_iff : 1 ≤ Pr[⊥ | mx] ↔ Pr[⊥ | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probFailure, or_false, eq_comm]

end bounds

section LawfulProbFailure

/-- Class for `HasEvalDist` instances that assign full failure chance to `failure`. -/
class LawfulProbFailure (m : Type _ → Type _) [AlternativeMonad m] [HasEvalDist m] where
    probFailure_failure {α : Type _} : Pr[⊥ | (failure : m α)] = 1

export LawfulProbFailure (probFailure_failure)

attribute [simp] probFailure_failure

end LawfulProbFailure

section bind

variable (mx : m α) (my : α → m β)

lemma probOutput_bind_eq_tsum (y : β) :
    Pr[= y | mx >>= my] = ∑' x : α, Pr[= x | mx] * Pr[= y | my x] := by
  simp [probOutput, evalDist_bind, tsum_option _ ENNReal.summable, Option.elimM]

end bind

lemma probOutput_true_eq_probEvent {α} {m : Type → Type u} [Monad m] [HasEvalDist m]
    (mx : m α) (p : α → Prop) : Pr{let x ← mx}[p x] = Pr[p | mx] := by
  rw [probEvent_eq_tsum_indicator]
  rw [probOutput_bind_eq_tsum]
  refine tsum_congr fun α => ?_
  simp [Set.indicator]
  congr
  rw [eq_true_eq_id]
  rfl

namespace SPMF

instance : HasSupportM SPMF := sorry

/-- Add instance for `SPMF` just to give access to notation. -/
instance hasEvalDist : HasEvalDist SPMF where
  evalDist := MonadHom.id SPMF
  support_eq := sorry

variable (p : SPMF α) (x : α)

@[simp] lemma evalDist_eq : evalDist p = p := rfl

@[simp] lemma probOutput_eq : probOutput p = p := rfl

@[simp] lemma probEvent_eq : probEvent p = p.run.toOuterMeasure ∘ Set.image some := rfl

@[simp] lemma probFailure_eq : probFailure p = p.run none := rfl

end SPMF

namespace PMF

instance hasSupportM : HasSupportM PMF := sorry

noncomputable instance hasEvalDist : HasEvalDist PMF where
  evalDist := MonadHom.ofLift PMF SPMF
  support_eq := sorry

variable (p : PMF α) (x : α)

@[simp] lemma evalDist_eq : evalDist p = liftM p := rfl

@[simp] lemma probOutput_eq : probOutput p = p := by
  refine funext fun x => ?_
  simp only [probOutput_def, evalDist_eq, OptionT.run_monadLift, monadLift_self]
  refine (PMF.map_apply _ _ _).trans ?_
  refine (tsum_eq_single x ?_).trans ?_
  · simp
    refine fun x h h' => ?_
    refine (h h'.symm).elim
  simp only [↓reduceIte]

@[simp] lemma probEvent_eq : probEvent p = p.toOuterMeasure := by
  refine funext fun x => ?_
  simp [probEvent_def, monad_map_eq_map]
  rw [Set.preimage_image_eq _ (Option.some_injective α)]
  rfl

@[simp] lemma probFailure_eq : probFailure p = 0 := by
    simp [probFailure, PMF.monad_map_eq_map]

end PMF
