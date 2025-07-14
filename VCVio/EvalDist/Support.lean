/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.SPMF
import ToMathlib.Control.MonadHom

/-!
# Support of a Monadic Computation

-/

open ENNReal

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

/-- Class for monads with a lawful embedding into `Set`, representing the possible outputs
for the computation. dt: should be `m →ₘ Set` extended
For monads like `StateM` should consider all possible input states. -/
class HasSupportM (m : Type u → Type v) [Monad m] where
  support {α : Type u} (mx : m α) : Set α
  support_pure {α : Type u} (x : α) : support (pure x : m α) = {x}
  support_bind {α β : Type u} (mx : m α) (my : α → m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x)

export HasSupportM (support support_pure support_bind)
attribute [simp] support_pure support_bind

-- lemma support_def (mx : m α) :
--     support mx = {x | Pr[= x | mx] ≠ 0} := rfl

-- lemma mem_support_iff (mx : m α) (x : α) :
--     x ∈ support mx ↔ Pr[= x | mx] ≠ 0 := Iff.rfl

-- @[simp] lemma support_pure (x : α) :
--     support (pure x : m α) = {x} := by
--   simp [support, probOutput_pure_eq_indicator]

-- @[simp] lemma support_bind (mx : m α) (my : α → m β) :
--     support (mx >>= my) = ⋃ x ∈ support mx, support (my x) := sorry

-- lemma mem_support_bind_iff (mx : m α) (my : α → m β) (y : β) :
--     y ∈ support (mx >>= my) ↔ ∃ x ∈ support mx, y ∈ support (my x) := by simp

-- @[simp] lemma support_eqRec (mx : m α) (h : α = β) :
--     support (h ▸ mx) = h.symm ▸ support mx := by induction h; rfl

-- @[simp] lemma support_map [LawfulMonad m] (mx : m α) (f : α → β) :
--     support (f <$> mx) = f '' support mx := by
--   simp [map_eq_bind_pure_comp, Set.ext_iff]
--   aesop

-- lemma mem_support_map [LawfulMonad m] {mx : m α} {x : α} (hx : x ∈ support mx)
--     (f : α → β) : f x ∈ support (f <$> mx) := by aesop

-- @[simp] lemma support_ite (p : Prop) [Decidable p] (mx mx' : m α) :
--     support (if p then mx else mx') = if p then support mx else support mx' :=
--   apply_ite support p mx mx'

-- @[simp] lemma support_failure {m : Type _ → Type _}
--     [AlternativeMonad m] [HasEvalDist m] [LawfulProbFailure m] :
--     support (failure : m α) = ∅ := sorry

namespace OptionT



end OptionT
