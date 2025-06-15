/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Basic

/-!
# Probability Distributions of Monadic Computations

TODO: it's not good that we have extra `rfl` calls in certain proofs.
Improving lower level definitions should automate that.
-/

open ENNReal

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m] [HasEvalDist m]

section pure

@[simp] lemma evalDist_pure (x : α) : Pr[(pure x : m α)] = PMF.pure (some x) :=
  MonadHom.mmap_pure _ x

/-- TODO: we really need to globally standardize the "direction" of equality in things like this -/
@[simp] lemma probOutput_pure [DecidableEq α] (x y : α) :
    Pr[= x | (pure y : m α)] = if x = y then 1 else 0 := by
  simp [probOutput_def, OptionT.run]

@[simp] lemma probEvent_pure (p : α → Prop) [DecidablePred p] (y : α) :
    Pr[p | (pure y : m α)] = if p y then 1 else 0 := by
  simp [probEvent_def, OptionT.run]

@[simp] lemma probFailure_pure (y : α) :
    Pr[⊥ | (pure y : m α)] = 0 := by
  simp [probFailure_def, OptionT.run]

@[simp] lemma evalDist_comp_pure : evalDist ∘ (pure : α → m α) = pure := by
  simp only [Function.comp_def, evalDist_pure]
  rfl

@[simp] lemma evalDist_comp_pure' (f : α → β) : evalDist ∘ (pure : β → m β) ∘ f = pure ∘ f := by
  simp only [← Function.comp_assoc, evalDist_comp_pure]

end pure

section bind

variable (mx : m α) (my : α → m β)

@[simp] lemma evalDist_bind : Pr[mx >>= my] = Pr[mx] >>= fun x => Pr[my x] :=
  MonadHom.mmap_bind _ mx my

lemma probOutput_bind_eq_tsum (y : β) :
    Pr[= y | mx >>= my] = ∑' x : α, Pr[= x | mx] * Pr[= y | my x] := by
  simp [probOutput, evalDist_bind, tsum_option _ ENNReal.summable, Option.elimM]

end bind

section map

@[simp] lemma evalDist_map [LawfulMonad m] (mx : m α) (f : α → β) :
    evalDist (f <$> mx) = f <$> (evalDist mx) := by
  simp [map_eq_bind_pure_comp]; rfl

@[simp] lemma evalDist_comp_map [LawfulMonad m] (mx : m α) :
    evalDist ∘ (fun f => f <$> mx) = fun f : (α → β) => f <$> evalDist mx := by simp [funext_iff]

end map

section seq

@[simp] lemma evalDist_seq [LawfulMonad m] (mf : m (α → β)) (mx : m α) :
    evalDist (mf <*> mx) = evalDist mf <*> evalDist mx := by simp [seq_eq_bind_map]

end seq
