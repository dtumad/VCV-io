/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
-- import Batteries.Control.OptionT
import Batteries.Control.Lemmas
import Batteries.Control.Lawful.MonadLift
import Mathlib.Control.Lawful

/-!
# Laws for Monads with Failure

Definitions for monads that also have an `Alternative` instance while sharing the underlying
`Applicative` instance, and a class `LawfulAlternative` for types where the `failure` and `orElse`
operations behave in a natural way. More specifically they satisfy:

* `f <$> failure = failure`
* `failure <*> x = failure`
* `x <|> failure = x`
* `failure <|> y = y`
* `x <|> y <|> z = (x <|> y) <|> z`
* `f <$> (x <|> y) = (f <$> x <|> f <$> y)`

`Option`/`OptionT` are the most basic examples, but transformers like `StateT` also preserve
the lawfulness of this on the underlying monad.

The law `x *> failure = failure` is true for monads like `Option` and `List` that don't
have any "side effects" to execution, but not for something like `OptionT` on some monads,
so we don't include this condition.

We also define a class `LawfulAlternativeLift` similar to `LawfulMonadLift` that states that
a lifting between monads preserves `failure` and `orElse`.

## Tags

monad, alternative, failure
-/

universe u v w

/-- `AlternativeMonad m` means that `m` has both a `Monad` and `Alternative` instance,
which both share the same underlying `Applicative` instance.
The main example is `Option`, but many monad transformers also preserve or add this structure. -/
class AlternativeMonad (m : Type u → Type v) extends Alternative m, Monad m

section LawfulAlternative

/-- `LawfulAlternative m` means that the `failure` operation on `m` behaves naturally
with respect to `map`, `seq`, and `orElse` operators. -/
class LawfulAlternative (m : Type u → Type v) [Alternative m] : Prop
    extends LawfulApplicative m where
  /-- Mapping the result of a failure is still a failure -/
  map_failure {α β} (f : α → β) : f <$> (failure : m α) = failure
  /-- Sequencing a `failure` call results in failure -/
  failure_seq {α β} (x : m α) : (failure : m (α → β)) <*> x = failure
  /-- `failure` is a right identity for `orElse`. -/
  orElse_failure {α} (x : m α) : (x <|> failure) = x
  /-- `failure` is a left identity for `orElse`. -/
  failure_orElse {α} (y : m α) : (failure <|> y) = y
  /-- `orElse` is associative. -/
  orElse_assoc {α} (x y z : m α) : (x <|> y <|> z) = ((x <|> y) <|> z)
  /-- `map` commutes with `orElse`. The stronger statement with `bind` generally isn't true -/
  map_orElse {α β} (x y : m α) (f : α → β) : f <$> (x <|> y) = (f <$> x <|> f <$> y)

export LawfulAlternative (map_failure failure_seq orElse_failure failure_orElse orElse_assoc
  map_orElse)
attribute [simp] map_failure failure_seq orElse_failure failure_orElse map_orElse

section Alternative

variable {m : Type _ → Type _} {α β}

@[simp] theorem mapConst_failure [Alternative m] [LawfulAlternative m] (y : β) :
    Functor.mapConst y (failure : m α) = failure := by
  rw [LawfulFunctor.map_const, Function.comp_apply, map_failure]

@[simp] theorem mapConst_orElse [Alternative m] [LawfulAlternative m] (x x' : m α) (y : β) :
    Functor.mapConst y (x <|> x') = (Functor.mapConst y x <|> Functor.mapConst y x') := by
  simp only [map_const, Function.comp_apply, map_orElse]

@[simp] theorem failure_seqLeft [Alternative m] [LawfulAlternative m] (x : m α) :
    (failure : m β) <* x = failure := by
  simp only [seqLeft_eq, map_failure, failure_seq]

@[simp] theorem failure_seqRight [Alternative m] [LawfulAlternative m] (x : m α) :
    (failure : m β) *> x = failure := by
  simp only [seqRight_eq, map_failure, failure_seq]

end Alternative

section AlternativeMonad

variable {m : Type _ → Type _} {α β}

@[simp] theorem failure_bind [AlternativeMonad m] [LawfulAlternative m] [LawfulMonad m]
    (x : α → m β) : failure >>= x = failure := by
  calc failure >>= x = (PEmpty.elim <$> failure) >>= x := by rw [map_failure]
    _ = failure >>= (x ∘ PEmpty.elim) := by rw [bind_map_left, Function.comp_def]
    _ = failure >>= (pure ∘ PEmpty.elim) := bind_congr fun a => a.elim
    _ = (PEmpty.elim <$> failure) >>= pure := by rw [bind_map_left, Function.comp_def]
    _ = failure := by rw [map_failure, bind_pure]

@[simp] theorem seq_failure [AlternativeMonad m] [LawfulAlternative m] [LawfulMonad m]
    (x : m (α → β)) : x <*> failure = x *> failure := by
  simp only [seq_eq_bind, map_failure, seqRight_eq, bind_map_left]

end AlternativeMonad

end LawfulAlternative

variable {m : Type _ → Type _} {n : Type _ → Type _}

/-- Type-class for monad lifts that preserve the `Alternative` operations. -/
class LawfulAlternativeLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [Alternative m] [Alternative n] [MonadLift m n] : Prop where
  /-- Lifting preserves `failure`. -/
  monadLift_failure {α} : monadLift (failure : m α) = (failure : n α)
  /-- Lifting preserves `orElse`. -/
  monadLift_orElse {α} (x y : m α) : monadLift (x <|> y) = (monadLift x <|> monadLift y : n α)

export LawfulAlternativeLift (monadLift_failure monadLift_orElse)

variable {α β}

@[simp] theorem liftM_failure [Alternative m] [Alternative n] [MonadLift m n]
    [LawfulAlternativeLift m n] : liftM (failure : m α) = (failure : n α) := monadLift_failure

@[simp] theorem liftM_orElse [Alternative m] [Alternative n] [MonadLift m n]
    [LawfulAlternativeLift m n] (x y : m α) : liftM (x <|> y) = (liftM x <|> liftM y : n α) :=
  monadLift_orElse x y

theorem monadLift_guard [AlternativeMonad m] [AlternativeMonad n] [MonadLift m n]
    [LawfulAlternativeLift m n] [LawfulMonadLift m n] (p : Prop) [Decidable p] :
    monadLift (guard p : m Unit) = (guard p : n Unit) := by
  simp only [guard, apply_ite (f := monadLift), liftM_pure, liftM_failure]

@[simp] theorem liftM_guard [AlternativeMonad m] [AlternativeMonad n] [MonadLift m n]
    [LawfulAlternativeLift m n] [LawfulMonadLift m n] (p : Prop) [Decidable p] :
    liftM (guard p : m Unit) = (guard p : n Unit) :=
  monadLift_guard p

theorem monadLift_optional [AlternativeMonad m] [AlternativeMonad n]
    [LawfulMonad m] [LawfulMonad n] [MonadLift m n] [LawfulAlternativeLift m n]
    [LawfulMonadLift m n]
    (x : m α) : monadLift (optional x) = optional (monadLift x : n α) := by
  simp only [optional, liftM_orElse, liftM_map, liftM_pure]

@[simp] theorem liftM_optional [AlternativeMonad m] [AlternativeMonad n]
    [LawfulMonad m] [LawfulMonad n] [MonadLift m n] [LawfulAlternativeLift m n]
    [LawfulMonadLift m n]
    (x : m α) : liftM (optional x) = optional (liftM x : n α) :=
  monadLift_optional x

namespace Option

instance : AlternativeMonad Option.{u} where

instance : LawfulAlternative Option.{u} where
  map_failure _ := rfl
  failure_seq _ := rfl
  orElse_failure := Option.orElse_none
  failure_orElse := Option.none_orElse
  orElse_assoc | some _, _, _ => rfl | none, _, _ => rfl
  map_orElse | some _ => by simp | none => by simp

@[simp] theorem elimM_pure [Monad m] [LawfulMonad m] (x : Option α) (y : m β)
    (z : α → m β) : Option.elimM (pure x) y z = Option.elim x y z := by
  simp [Option.elimM, Option.elim]

@[simp] theorem elimM_bind {γ} [Monad m] [LawfulMonad m] (x : m α) (f : α → m (Option β))
    (y : m γ) (z : β → m γ) : Option.elimM (x >>= f) y z = (do Option.elimM (f (← x)) y z) := by
  simp [Option.elimM]

@[simp] theorem elimM_map {γ} [Monad m] [LawfulMonad m] (x : m α) (f : α → Option β)
    (y : m γ) (z : β → m γ) : Option.elimM (f <$> x) y z = (do Option.elim (f (← x)) y z) := by
  simp [Option.elimM]

theorem monadLift_elimM [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [MonadLift m n] [LawfulMonadLift m n] (x : m (Option α)) (y : m β) (z : α → m β) :
      monadLift (Option.elimM x y z) =
        Option.elimM (monadLift x : n (Option α)) (monadLift y) (fun x => monadLift (z x)) :=
  (monadLift_bind _ _).trans (bind_congr fun | none => rfl | some _ => rfl)

@[simp]
theorem liftM_elimM [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [MonadLift m n] [LawfulMonadLift m n] (x : m (Option α)) (y : m β) (z : α → m β) :
      liftM (Option.elimM x y z) = Option.elimM (x : n (Option α)) (y) (fun x => z x) :=
  monadLift_elimM x y z

end Option

namespace OptionT

@[simp] theorem run_mapConst [Monad m] [LawfulMonad m] (x : OptionT m α) (y : β) :
    (Functor.mapConst y x).run = Option.map (Function.const α y) <$> x.run := run_map _ _

instance (m) [Monad m] : AlternativeMonad (OptionT m) where

instance (m) [Monad m] [LawfulMonad m] : LawfulMonad (OptionT m) :=
  LawfulMonad.mk'
    (id_map := by
      intros; apply OptionT.ext; simp only [OptionT.run_map]
      rw [map_congr, id_map]
      intro a; cases a <;> rfl)
    (bind_assoc := by
      refine fun _ _ _ => OptionT.ext ?_
      simp only [run_bind, Option.elimM, bind_assoc])
    (pure_bind := by intros; apply OptionT.ext; simp)


@[simp] theorem run_failure [Monad m] : (failure : OptionT m α).run = pure none := rfl

@[simp] theorem run_orElse [Monad m] (x : OptionT m α) (y : OptionT m α) :
    (x <|> y).run = Option.elimM x.run y.run (pure ∘ some) :=
  bind_congr fun | some _ => rfl | none => rfl

-- @[simp] theorem run_seq [Monad m] [LawfulMonad m] (f : OptionT m (α → β)) (x : OptionT m α) :
--     (f <*> x).run = Option.elimM f.run (pure none) (fun f => Option.map f <$> x.run) := by
--   simp only [seq_eq_bind, run_bind, run_map, Function.comp_def]

-- @[simp] theorem run_seqLeft [Monad m] [LawfulMonad m] (x : OptionT m α) (y : OptionT m β) :
--     (x <* y).run = Option.elimM x.run (pure none)
--       (fun x => Option.map (Function.const β x) <$> y.run) := by
--   simp [seqLeft_eq, seq_eq_bind, Option.elimM, Function.comp_def]

-- @[simp] theorem run_seqRight [Monad m] [LawfulMonad m] (x : OptionT m α) (y : OptionT m β) :
--     (x *> y).run = Option.elimM x.run (pure none) (Function.const α y.run) := by
--   simp only [seqRight_eq, run_seq, run_map, Option.elimM_map]
--   refine bind_congr (fun | some _ => by simp [Option.elim] | none => by simp [Option.elim])

instance (m) [Monad m] [LawfulMonad m] : LawfulAlternative (OptionT m) where
  map_failure _ := pure_bind _ _
  failure_seq _ := pure_bind _ _
  orElse_failure x := (bind_congr (fun | some _ => rfl | none => rfl)).trans (bind_pure x)
  failure_orElse _ := pure_bind _ _
  orElse_assoc _ _ _ := by
    simp only [OptionT.ext_iff, OptionT.run_orElse, Option.elimM, bind_assoc]
    refine bind_congr fun | some _ => by simp | none => rfl
  map_orElse x y f := by
    simp only [OptionT.ext_iff, run_map, run_orElse, map_bind, bind_map_left, Option.elimM]
    refine bind_congr fun | some _ => by simp | none => rfl

end OptionT

namespace StateT

variable {σ : Type u}

instance (m) [AlternativeMonad m] : AlternativeMonad (StateT σ m) where

instance (m) [AlternativeMonad m] [LawfulAlternative m] [LawfulMonad m] :
    LawfulAlternative (StateT σ m) where
  map_failure _ := StateT.ext fun _ => by simp only [run_map, run_failure, map_failure]
  failure_seq _ := StateT.ext fun _ => by simp only [run_seq, run_failure, failure_bind]
  orElse_failure _ := StateT.ext fun _ => orElse_failure _
  failure_orElse _ := StateT.ext fun _ => failure_orElse _
  orElse_assoc _ _ _ := StateT.ext fun _ => orElse_assoc _ _ _
  map_orElse _ _ _ := StateT.ext fun _ => by simp only [run_map, run_orElse, map_orElse]

instance (m) [AlternativeMonad m] [LawfulAlternative m] [LawfulMonad m] :
    LawfulAlternativeLift m (StateT σ m) where
  monadLift_failure {α} := StateT.ext fun s => by simp
  monadLift_orElse {α} x y := StateT.ext fun s => by simp

end StateT

namespace ReaderT

variable {ρ}

instance [AlternativeMonad m] : AlternativeMonad (ReaderT ρ m) where

instance [AlternativeMonad m] [LawfulAlternative m] : LawfulAlternative (ReaderT ρ m) where
  map_failure _ := ReaderT.ext fun _ => map_failure _
  failure_seq _ := ReaderT.ext fun _ => failure_seq _
  orElse_failure _ := ReaderT.ext fun _ => orElse_failure _
  failure_orElse _ := ReaderT.ext fun _ => failure_orElse _
  orElse_assoc _ _ _ := ReaderT.ext fun _ => orElse_assoc _ _ _
  map_orElse _ _ _ := ReaderT.ext fun _ => by simp only [run_map, run_orElse, map_orElse]

instance [AlternativeMonad m] : LawfulAlternativeLift m (ReaderT ρ m) where
  monadLift_failure {α} := ReaderT.ext fun s => by simp
  monadLift_orElse {α} x y := ReaderT.ext fun s => by simp

end ReaderT

namespace StateRefT'

variable {ω σ}

instance [AlternativeMonad m] : AlternativeMonad (StateRefT' ω σ m) where

instance [AlternativeMonad m] [LawfulAlternative m] :
    LawfulAlternative (StateRefT' ω σ m) :=
  inferInstanceAs (LawfulAlternative (ReaderT _ _))

instance [AlternativeMonad m] : LawfulAlternativeLift m (StateRefT' ω σ m) :=
  inferInstanceAs (LawfulAlternativeLift m (ReaderT _ _))

end StateRefT'
