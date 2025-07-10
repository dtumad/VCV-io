/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Basic


/-!
# Support of Probabalistic Computations

This file defines the support of a computation with an evaluation distribution.
The definition of `support` works for any monad with a `HasEvalDist` instance,
using the embedding as a distribution to check if any given output is possible or not.

TODO(dt): A typeclass `HasFinSupport` can be implemented when only finitely many outputs exist.
TODO(dt): Specific lemmas for `OptionT` and failure.
-/

open ENNReal

universe u v w

variable {α β γ : Type u} {m : Type u → Type v}
  [Monad m] [HasEvalDist m]

namespace HasEvalDist

/-- The `support` of a computation `mx` is the set of outputs with non-zero `probOutput`.
TODO(dt): This should actually be a monad morphism-/
def support {m : Type u → Type v} [Monad m] [HasEvalDist m]
    (mx : m α) : Set α := {x | Pr[= x | mx] ≠ 0}

lemma support_def (mx : m α) :
    support mx = {x | Pr[= x | mx] ≠ 0} := rfl

lemma mem_support_iff (mx : m α) (x : α) :
    x ∈ support mx ↔ Pr[= x | mx] ≠ 0 := Iff.rfl

@[simp] lemma support_pure (x : α) :
    support (pure x : m α) = {x} := by
  simp [support, probOutput_pure_eq_indicator]

@[simp] lemma support_bind (mx : m α) (my : α → m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x) := sorry

lemma mem_support_bind_iff (mx : m α) (my : α → m β) (y : β) :
    y ∈ support (mx >>= my) ↔ ∃ x ∈ support mx, y ∈ support (my x) := by simp

@[simp] lemma support_eqRec (mx : m α) (h : α = β) :
    support (h ▸ mx) = h.symm ▸ support mx := by induction h; rfl

@[simp] lemma support_map [LawfulMonad m] (mx : m α) (f : α → β) :
    support (f <$> mx) = f '' support mx := by
  simp [map_eq_bind_pure_comp, Set.ext_iff]
  aesop

lemma mem_support_map [LawfulMonad m] {mx : m α} {x : α} (hx : x ∈ support mx)
    (f : α → β) : f x ∈ support (f <$> mx) := by aesop

@[simp] lemma support_ite (p : Prop) [Decidable p] (mx mx' : m α) :
    support (if p then mx else mx') = if p then support mx else support mx' :=
  apply_ite support p mx mx'

end HasEvalDist

namespace OptionT



end OptionT
