
/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ToMathlib.Control.FreeMonad
import ToMathlib.Control.LawfulFailure
import ToMathlib.Control.MonadHom
import ToMathlib.General

/-!
# Lemmas about `OptionT`
-/

universe u v w

namespace Option

instance : LawfulFailure Option where
  fail_bind' _ := rfl

end Option

namespace OptionT

variable {m : Type u → Type v}
  {n : Type u → Type w}
  (f : {α : Type u} →  m α → n α) {α β γ : Type u}

-- @[simp]
lemma monad_pure_eq_pure [Monad m] (x : α) :
    (pure x : OptionT m α) = OptionT.pure x := rfl

-- @[simp]
lemma monad_bind_eq_bind [Monad m] (x : OptionT m α) (y : α → OptionT m β) :
    x >>= y = OptionT.bind x y := rfl

lemma run_seq {α β : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (f : OptionT m (α → β)) (x : OptionT m α) :
    (f <*> x).run = (do let g ← f.run; match g with
      | some g => Option.map g <$> x.run
      | none => pure none) := by
  simp only [seq_eq_bind_map, run_bind, run_map]
  exact bind_congr fun | some x => rfl | none => rfl

@[simp]
lemma run_fail {α : Type u} {m : Type u → Type v} [Monad m] :
    (Failure.fail : OptionT m α).run = pure none := rfl

@[simp]
lemma run_failure {α : Type u} {m : Type u → Type v} [Monad m] :
    (failure : OptionT m α).run = pure none := rfl

instance (m : Type u → Type v) [Monad m] [LawfulMonad m] : LawfulFailure (OptionT m) where
  fail_bind' g := OptionT.ext (by simp)

lemma liftM_def {m : Type u → Type v} [Monad m] {α : Type u}
    (x : m α) : (x : OptionT m α) = OptionT.lift x := rfl

section mapM

/-- Canonical lifting of a map from `m α → n α` to one from `OptionT m α → n α`
given an `Alternative n` instance to handle failure. -/
protected def mapM {m : Type u → Type v} {n : Type u → Type w}
    [Failure n] [Monad n] (f : {α : Type u} → m α → n α)
    {α : Type u} (x : OptionT m α) : n α :=
  do match (← f x.run) with | some x => return x | none => Failure.fail

protected def mapM' {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [Failure n] [Monad n] [LawfulMonad n] [LawfulFailure n]
    (f : m →ᵐ n) : OptionT m →ᵐ n where
  toFun x := do match (← f x.run) with
    | some x => return x
    | none => Failure.fail
  toFun_pure' x := by
    simp
  toFun_bind' x y := by
    simp
    congr 1
    ext x
    cases x
    simp
    simp

@[simp]
lemma mapM'_lift {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [Failure n] [Monad n] [LawfulMonad n] [LawfulFailure n]
    (f : m →ᵐ n) (x : m α) : OptionT.mapM' f (OptionT.lift x) = f x := by
  simp [OptionT.mapM', OptionT.lift]

@[simp]
lemma mapM'_failure {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [Failure n] [Monad n] [LawfulMonad n] [LawfulFailure n]
    (f : m →ᵐ n) : OptionT.mapM' f (failure : OptionT m α) = Failure.fail := by
  simp [OptionT.mapM']

lemma mapM_pure [Monad m] [Monad n] [LawfulMonad n] [Failure n] [LawfulFailure n]
    (h : ∀ {α} (x : α), f (OptionT.pure x).run = pure x) (x : α) :
    OptionT.mapM f (pure x : OptionT m α) = pure x := by
  simp [OptionT.mapM, h, OptionT.monad_pure_eq_pure]

end mapM

end OptionT
