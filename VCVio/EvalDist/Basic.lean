/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, František Silváši
-/
import VCVio.EvalDist.SPMF
import ToMathlib.Control.MonadHom


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

/-- The monad `m` has a well-behaved embedding into the `SPMF` monad, implemented as a `MonadHom`.
In particular the lifting respects `return`, `bind`, `map`, etc.

We choose this over a `MonadLift` to be more explicit about which monads should actually
have such a distribution and prevent over-aggressive type-class lifting. -/
class HasEvalDist (m : Type u → Type v) [Monad m] extends MonadHom m SPMF

/-- Probability distribution of a computation `mx` induced by a `HasEvalDist` instance. -/
def evalDist [h : HasEvalDist m] (mx : m α) : SPMF α :=
  h.toFun mx

/-- Probability that a computation `mx` returns the value `x`. -/
def probOutput [HasEvalDist m] (mx : m α) (x : α) : ℝ≥0∞ :=
  evalDist mx x

/-- Probability that a computation `mx` outputs a value satisfying `p`. -/
noncomputable def probEvent [HasEvalDist m] (mx : m α) (p : α → Prop) : ℝ≥0∞ :=
  (evalDist mx).run.toOuterMeasure (some '' {x | p x})

/-- Probability that a compuutation `mx` will fail to return a value. -/
def probFailure [HasEvalDist m] (mx : m α) : ℝ≥0∞ :=
  (evalDist mx).run none

/-- Probability distribution associated to a computation. -/
notation "Pr[" mx "]" => evalDist mx

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

/-- Simple unit for all the different probability notations. -/
example {m : Type → Type u} [Monad m] [HasEvalDist m] (mx : m ℕ) : Unit :=
  let _ : SPMF ℕ := Pr[mx]
  let _ : ℝ≥0∞ := Pr[= 10 | mx]
  let _ : ℝ≥0∞ := Pr[fun x => x^2 + x < 10 | mx]
  let _ : ℝ≥0∞ := Pr[x^2 + x < 10 | x ← mx]
  let _ : ℝ≥0∞ := Pr{let x ← mx}[x = 10]
  let _ : ℝ≥0∞ := Pr[⊥ | mx]
  ()

variable [hm : HasEvalDist m]

lemma evalDist_def (mx : m α) :
    Pr[mx] = hm.toFun mx := rfl

lemma probOutput_def (mx : m α) (x : α) :
    Pr[= x | mx] = Pr[mx] x := rfl

lemma probEvent_def (mx : m α) (p : α → Prop) :
    Pr[p | mx] = Pr[mx].run.toOuterMeasure (some '' {x | p x}) := rfl

lemma probFailure_def (mx : m α) :
    Pr[⊥ | mx] = Pr[mx].run none := rfl

section sum_indicator

lemma probEvent_eq_tsum_indicator (mx : m α) (p : α → Prop) :
    Pr[p | mx] = ∑' x : α, {x | p x}.indicator (Pr[= · | mx]) x := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, Set.indicator_image (Option.some_injective _),
    tsum_option _ ENNReal.summable, probOutput_def, Function.comp_def]

end sum_indicator

section sum_ite

lemma probEvent_eq_tsum_ite (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = ∑' x : α, if p x then Pr[= x | mx] else 0 := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, tsum_option _ ENNReal.summable,
    Set.indicator, probOutput_def]

lemma probEvent_eq_sum_finType_ite [Fintype α] (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = ∑ x : α, if p x then Pr[= x | mx] else 0 := by
  rw [probEvent_eq_tsum_ite, tsum_eq_sum]
  simp

end sum_ite

@[simp] lemma probFailure_add_tsum_probOutput (oa : m α) :
    Pr[⊥ | oa] + ∑' x, Pr[= x | oa] = 1 :=
  (tsum_option _ ENNReal.summable).symm.trans (evalDist oa).tsum_coe

@[simp] lemma tsum_probOutput_add_probFailure (oa : m α) :
    ∑' x, Pr[= x | oa] + Pr[⊥ | oa] = 1 :=
  by rw [add_comm, probFailure_add_tsum_probOutput]

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

namespace SPMF

/-- Add instance for `SPMF` just to give access to notation, using identity morphism. -/
instance hasEvalDist : HasEvalDist SPMF := HasEvalDist.mk (MonadHom.id SPMF)

variable (p : SPMF α) (x : α)

@[simp] lemma evalDist_eq : evalDist p = p := rfl

@[simp] lemma probOutput_eq : probOutput p = p := rfl

@[simp] lemma probEvent_eq : probEvent p = p.run.toOuterMeasure ∘ Set.image some := rfl

@[simp] lemma probFailure_eq : probFailure p = p.run none := rfl

end SPMF

namespace PMF

/-- Induced distribution on `PMF` by the natural lifting into `SPMF`. -/
noncomputable instance hasEvalDist : HasEvalDist PMF :=
  HasEvalDist.mk (MonadHom.ofLift PMF SPMF)

variable (p : PMF α) (x : α)

@[simp] lemma evalDist_eq : Pr[p] = liftM p := rfl

@[simp] lemma probOutput_eq : probOutput p = p := by
  refine funext fun x => ?_
  simp only [probOutput_def, evalDist_eq, monad_pure_eq_pure, monad_bind_eq_bind, OptionT.run_mk,
    pure_apply, Option.some.injEq, mul_ite, mul_one, mul_zero]
  simp
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

section SPMF

@[simp] lemma evalDist_liftM (px : PMF α) :
    Pr[(liftM px : SPMF α)] = Pr[px] := rfl

@[simp] lemma probOutput_liftM (px : PMF α) (x : α) :
    Pr[= x | (liftM px : SPMF α)] = Pr[= x | px] := rfl

@[simp] lemma probEvent_liftM (px : PMF α) (p : α → Prop) :
    Pr[p | (liftM px : SPMF α)] = Pr[p | px] := rfl

@[simp] lemma probFailure_liftM (px : PMF α) :
    Pr[⊥ | (liftM px : SPMF α)] = 0 := by simp [PMF.monad_map_eq_map]

end SPMF

end PMF
