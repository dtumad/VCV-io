/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.Asymptotics.Negligible

/-!
# Hard Relations

This file defines a typeclass `HardRelation X W r` for relations `r : X → W → Prop`
that are "hard" in the sense that given `x : X` no polynomial adversary can find `w : W`
such that `r x w` holds.

In the actual implementation all of these are indexed by some security parameter.
-/

open OracleSpec OracleComp OracleAlg BigOperators ENNReal

/-- A reltation `r` is generable if there is an efficient algorithm `gen`
that produces values satisfying the relation. For example "is discrete log of" is generable
because we can choose the exponent first (see `HardHomogeneousSpace`). -/
class GenerableRelation (X W : ℕ → Type)
    (r : {n : ℕ} → X n → W n → Bool) where
  gen (n : ℕ) : OracleComp unifSpec (X n × W n)
  gen_sound (n : ℕ) (x : X n) (w : W n) :
    (x, w) ∈ (gen n).support → r x w

/-- Experiment for checking whether an adversary `adv` can generate `w : W n`,
given a random `x : X n`, such that `r x w` holds. For example the discrete log assumption says
that this is hard for the relation "is the discrete log of". -/
def hardRelationExp (X W : ℕ → Type) [Π n, Fintype (X n)] [Π n, Inhabited (X n)]
    [Π n, SelectableType (X n)] (r : {n : ℕ} → X n → W n → Bool)
    (adv : SecAdv (λ _ ↦ unifSpec) X W) : SecExp (λ _ ↦ unifSpec) where
  main := λ n ↦ do
    let x ←$ᵗ X n
    let w ← adv.run n x
    return r x w
  __ := baseOracleAlg

/-- A hard relation `r : X n → W n → Prop` is one where it is easy to generate a pair `(x, w)`
with `r x w` holding, but given `x` it is hard to find `w` where `r` holds. -/
class HardRelation  (X W : ℕ → Type) [Π n, Fintype (X n)]
    [Π n, Inhabited (X n)] [Π n, SelectableType (X n)]
    (r : {n : ℕ} → X n → W n → Bool)
    extends GenerableRelation X W r where
  relation_hard : ∀ (adv : SecAdv (λ _ ↦ unifSpec) X W),
    negligible (hardRelationExp X W r adv).advantage
