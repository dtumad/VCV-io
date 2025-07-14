/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, František Silváši
-/
import VCVio.EvalDist.HasEvalDist

/-!
# Finite Distribution Semantics for Monadic Computation

This file defines a typeclass `HasFinEvalDist` extending the base class
with the fact that the support is finite.

While this could just extend `HasSupportM`, this leads to diamond issues,
and we generally only use it to simplify `probOutput` type calculations by
reducing to finite sums, so generally isn't really needed.

-/

open ENNReal

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

/-- The monad `m` has a well-behaved embedding into the `SPMF` monad.
TODO: modify this to extend `MonadHom` to get some lemmas for free. -/
class HasFinEvalDist (m : Type u → Type v) [Monad m]
    extends HasEvalDist m where
  finSupport {α : Type u} (mx : m α) : Finset α
  mem_finSupport_iff {α : Type u} (mx : m α) (x : α) :
    x ∈ finSupport mx ↔ x ∈ support mx

export HasFinEvalDist (finSupport mem_finSupport_iff)
attribute [simp] mem_finSupport_iff
