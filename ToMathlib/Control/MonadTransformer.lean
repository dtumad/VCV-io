/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
-- import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.Control.Lawful -- Enables inferInstance : LawfulMonad (OptionT m)
import ToMathlib.Control.Lawful.MonadLift

/-!
# Monad transformers

Taken from [Zulip thread](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/MonadFunctor.20misunderstanding.20or.20bug.3F/near/477088609).

-/

universe u v w

/--
A function for lifting a computation from an inner `Monad` to an outer `Monad`.
Like Haskell's [`MonadTrans`], this is a functorial version of `MonadLift`.

  [`MonadTrans`]: https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Class.html
-/
class MonadTransformer (t : (Type u → Type v) → Type u → Type w) where
  mapMonad (m) [Monad m] : Monad (t m)
  transform (m) [Monad m] : MonadLift m (t m)

variable {t : (Type u → Type v) → Type u → Type w} {m : Type u → Type v} {α β ρ ε σ : Type u}

instance [MonadTransformer t] [Monad m] : Monad (t m) := MonadTransformer.mapMonad m

@[always_inline, inline, simp]
abbrev MonadTransformer.liftOf [MonadTransformer t] (m) [Monad m] : m α → t m α :=
  (transform m).monadLift

@[always_inline, inline, simp]
abbrev MonadTransformer.lift [MonadTransformer t] {m} [Monad m] : m α → t m α :=
  liftOf m

instance : MonadTransformer (ReaderT ρ) where
  mapMonad _ := inferInstance
  transform := inferInstance

instance : MonadTransformer (ExceptT ε) where
  mapMonad _ := inferInstance
  transform _ := inferInstance

instance : MonadTransformer (StateT σ) where
  mapMonad _ := inferInstance
  transform _ := inferInstance

instance : MonadTransformer OptionT where
  mapMonad _ := inferInstance
  transform _ := inferInstance

/--
The `MonadTransformer` typeclass only contains the operations of a monad transformer.
`LawfulMonadTransformer` further asserts that these operations satisfy the laws of a monad transformer:
```
liftOf m (pure x) = pure x
liftOf m x >>= liftOf m ∘ f = liftOf m (x >>= f)
```
-/
class LawfulMonadTransformer (t) [MonadTransformer t] : Prop where
  monad_functor {m} [Monad m] [LawfulMonad m] : LawfulMonad (t m)
  lift_pure {m} [Monad m] [LawfulMonad m] {α} (x : α) :
    ‹MonadTransformer t›.liftOf m (pure x) = pure x
  lift_bind {m} [Monad m] [LawfulMonad m] {α β} (x : m α) (f : α → m β) :
    ‹MonadTransformer t›.lift x >>= MonadTransformer.lift ∘ f = MonadTransformer.lift (x >>= f)

section
attribute [local simp] MonadLift.monadLift Bind.bind

instance : LawfulMonadTransformer (ReaderT ρ) where
  monad_functor := inferInstance
  lift_pure _ := rfl
  lift_bind _ _ := rfl

instance : LawfulMonadTransformer (ExceptT ε) where
  monad_functor := inferInstance
  lift_pure _ := map_pure _ _
  lift_bind _ _ := by
    dsimp [ExceptT.lift]
    rw [map_bind]
    exact bind_map_left _ _ _

instance : LawfulMonadTransformer (StateT σ) where
  monad_functor := inferInstance
  lift_pure _ := funext fun _ => pure_bind _ _
  lift_bind _ _ := by
    funext
    dsimp [StateT.lift, StateT.bind]
    rw [bind_pure_comp, bind_map_left]
    rw [bind_pure_comp, map_bind]
    congr
    funext
    exact bind_pure_comp _ _

instance : LawfulMonadTransformer OptionT where
  monad_functor := inferInstance
  lift_pure _ := pure_bind _ _
  lift_bind _ _ := by
    dsimp [OptionT.lift, OptionT.bind, OptionT.mk]
    rw [bind_pure_comp, bind_map_left]
    rw [bind_pure_comp, map_bind]
    congr
    funext
    exact bind_pure_comp _ _

end

-- /--
-- The `MonadLift` typeclass only contains the operations of a monad lift.
-- `LawfulMonadLift` further asserts that these operations satisfy the laws of a monad lift:
-- ```
-- monadLift (pure x) = pure x
-- monadLift x >>= monadLift ∘ f = monadLift (x >>= f)
-- ```
-- -/
-- class LawfulMonadLift (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
--     [MonadLift m n] : Prop where
--   lift_pure (x : α) : ‹MonadLift m n›.monadLift (pure x) = pure x
--   lift_bind (x : m α) (f : α → m β)
--     : ‹MonadLift m n›.monadLift x >>= monadLift ∘ f = monadLift (x >>= f)

namespace MonadTransformer

instance [MonadTransformer t] [Monad m] : MonadLift m (t m) := MonadTransformer.transform m

instance [MonadTransformer t] [Monad m] [LawfulMonad m] [LawfulMonadTransformer t]
    : LawfulMonadLift m (t m) where
  monadLift_pure := LawfulMonadTransformer.lift_pure
  monadLift_bind := LawfulMonadTransformer.lift_bind

end MonadTransformer
