/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SigmaAlg
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.Coercions.Append

/-!
# Fiat-Shamir Transform

This file defines a basic version of the Fiat-Shamir transform on sigma protocols.
For simplicity we construct signature schemes rather than general proofs of knowledge.
-/

universe u v

-- TODO
open OracleComp OracleSpec

-- variable {ι : Type} (spec : ℕ → OracleSpec ι)
--     (X W : ℕ → Type) (p : {n : ℕ} → X n → W n → Bool)
--     (PC SC Ω P M : ℕ → Type)
--     [Π n, Inhabited (Ω n)] [Π n, DecidableEq (Ω n)]
--     [Π n, Fintype (Ω n)] [Π n, SelectableType (Ω n)]
--     [Π n, DecidableEq (PC n)] [Π n, DecidableEq (M n)]
--     [Π n, Fintype (X n)] [Π n, Inhabited (X n)] [Π n, SelectableType (X n)]
--     [Π n, Fintype (W n)] [Π n, Inhabited (W n)] [Π n, SelectableType (W n)]


section genrel

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type v} {σ X W : Type}
    {p : X → W → Bool} {PC SC Ω P : Type} [Monad m]
    [SelectableType X] [SelectableType W] (M : Type)


-- /-- Given a Σ-protocol we get a signature algorithm by using a random oracle to generate
-- challenge values for the Σ-protocol, including the message in the hash input. -/
-- def FiatShamirTransform (sigmaAlg : SigmaAlg spec σ X W p PC SC Ω P)
--     (M : Type) :
--     SignatureAlg spec σ M X W (PC × P) := sorry

structure GenerableRelation (m : Type → Type u) [Monad m]
    (X W : Type) (r : X → W → Bool)
    [SelectableType X] [SelectableType W]
    extends ExecutionMethod m where
  gen : m (X × W)
  gen_sound (x : X) (w : W) :
    (x, w) ∈ (exec gen).support → r x w
  gen_uniform_right :
    exec (Prod.fst <$> gen) = $ᵗ X
  gen_uniform_left :
    exec (Prod.snd <$> gen) = $ᵗ W

end genrel

variable {ι : Type} {spec : OracleSpec ι} {σ X W PC SC Ω P : Type}
    {p : X → W → Bool} [SelectableType X] [SelectableType W]
    [DecidableEq PC] [DecidableEq Ω] [SelectableType Ω]

def FiatShamir (sigmaAlg : SigmaAlg ProbComp X W PC SC Ω P p)
    (hr : GenerableRelation ProbComp X W p) (M : Type) [DecidableEq M] :
    SignatureAlg (OracleComp (unifSpec ++ₒ (M × PC →ₒ Ω)))
      (M := M) (PK := X) (SK := W) (S := PC × P) where
  -- Use the existing algorithm for generating relation members
  keygen := hr.gen
  -- Sign by running the sigma protocol using a hash as the challenge
  sign := fun pk sk m => do
    let (c, e) ← sigmaAlg.commit pk sk
    let r : Ω ← (query () (m, c) : OracleQuery (M × PC →ₒ Ω) Ω)
    let s ← sigmaAlg.respond pk sk e r
    return (c, s)
  -- Verify a signature by checking the challenge returned by the random oracle
  verify := fun pk m (c, s) => do
    let r' ← (query () (m, c) : OracleQuery (M × PC →ₒ Ω) Ω)
    return sigmaAlg.verify pk c r' s
  exec comp := sigmaAlg.exec sorry
  lift_probComp := sorry
  exec_lift_probComp := sorry

namespace FiatShamir

-- TODO

end FiatShamir
