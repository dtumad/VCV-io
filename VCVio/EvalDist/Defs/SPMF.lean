-- dt: This should all end up in mathlib
/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, František Silváši
-/
import Mathlib.Probability.ProbabilityMassFunction.Monad
import ToMathlib.General
import Batteries.Control.AlternativeMonad

open ENNReal

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

/-- Subprobability distribution. -/
@[reducible] def SPMF : Type u → Type u := OptionT PMF

namespace SPMF

lemma tsum_run_some_eq_one_sub (p : SPMF α) :
    ∑' x, p.run (some x) = 1 - p.run none := by
  rw [p.tsum_coe.symm.trans (tsum_option _ ENNReal.summable)]
  exact (ENNReal.add_sub_cancel_left (PMF.apply_ne_top p none)).symm

@[simp] lemma tsum_run_some_ne_top (p : SPMF α) :
    ∑' x, p.run (some x) ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (p.tsum_run_some_eq_one_sub ▸ tsub_le_self)

lemma run_none_eq_one_sub (p : SPMF α) :
    p.run none = 1 - ∑' x, p.run (some x) := by
  rw [p.tsum_coe.symm.trans (tsum_option _ ENNReal.summable)]
  refine ENNReal.eq_sub_of_add_eq ?_ rfl
  simp only [ne_eq, tsum_run_some_ne_top, not_false_eq_true]

@[simp] lemma run_none_ne_top (p : SPMF α) : p.run none ≠ ⊤ := PMF.apply_ne_top p none

@[ext] lemma ext {p q : SPMF α} (h : ∀ x : α, p.run (some x) = q.run (some x)) : p = q :=
  PMF.ext fun
    | some x => h x
    | none =>  calc p.run none
        _ = 1 - ∑' x, p.run (some x) := by rw [run_none_eq_one_sub]
        _ = 1 - ∑' x, q.run (some x) := by simp only [h]
        _ = q.run none := by rw [run_none_eq_one_sub]

-- Should we do it this way or add the instance on `Option α` instead?
instance : FunLike (SPMF α) α ENNReal where
  coe sp x := sp.run (some x)
  coe_injective' p q h := by simpa [SPMF.ext_iff] using congr_fun h

@[simp] lemma apply_eq_run_some (p : SPMF α) (x : α) : p x = p.run (some x) := rfl

lemma apply'_none_eq_run (p : SPMF α) :
    let p' : PMF (Option α) := p
    p' none = p.run none := rfl

end SPMF
