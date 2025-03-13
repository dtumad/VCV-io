/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.SimSemantics.QueryTracking.LoggingOracle
import VCVio.OracleComp.SimSemantics.Append

/-!
# Asymmetric Encryption Schemes.

This file defines a type `AsymmEncAlg spec σ M PK SK C` to represent an protocol
for asymmetric encryption using oracles in `spec`, with message space `M`,
public/secret keys `PK` and `SK`, and ciphertext space `C`.
-/

universe u v

open OracleSpec OracleComp

/-- Signature algorithm with access to oracles in `spec` (simulated with state `σ`),
where `M` is the space of messages, `PK`/`SK` are the spaces of the public/private keys,
and `S` is the type of the final signature.
`em` is the execution monad used in the implementation of the oracles. -/
structure SignatureAlg {ι : Type u} (spec : OracleSpec ι) (m : Type → Type v)
    (M PK SK S : Type) extends ExecutionMethod spec m where
  keygen : OracleComp spec (PK × SK)
  sign (pk : PK) (sk : SK) (msg : M) : OracleComp spec S
  verify (pk : PK) (msg : M) (σ : S) : OracleComp spec Bool

namespace SignatureAlg

variable {ι : Type} {spec : OracleSpec ι} {em : Type → Type} {σ M PK SK S : Type}
  [AlternativeMonad em] [LawfulAlternative em]

section sound

def IsSound (sigAlg : SignatureAlg spec em M PK SK S) : Prop :=
  ∀ m : M, [= true | sigAlg.exec do
    let (pk, sk) ← sigAlg.keygen
    let sig ← sigAlg.sign pk sk m
    sigAlg.verify pk m sig] = 1

-- /-- Experiment to check that valid signatures succeed at being verified. -/
-- def soundnessExp (sigAlg : SignatureAlg spec σ M PK SK S)
--     (m : M) : SecExp spec σ where
--   main := do
--     let (pk, sk) ← sigAlg.keygen
--     let sig ← sigAlg.sign pk sk m
--     let b ← sigAlg.verify pk m sig
--     guard b
--   __ := sigAlg

-- /-- A signature algorithm is complete if valid signatures always verify. -/
-- def IsComplete (sigAlg : SignatureAlg spec σ M PK SK S) : Prop :=
--   ∀ m : M, (sigAlg.soundnessExp m).advantage = 1

end sound

section unforgeable

variable [DecidableEq ι] [Inhabited S] [Fintype S] [DecidableEq S] [DecidableEq M]

def signingOracle (sigAlg : SignatureAlg spec em M PK SK S)
    (pk : PK) (sk : SK) : QueryImpl (M →ₒ S)
    (StateT (QueryLog (M →ₒ S)) (OracleComp spec)) where
  impl | query () m => do
    let σ ← sigAlg.sign pk sk m
    modifyGet λ log ↦ (σ, log.logQuery ⟨(), m⟩ σ)

abbrev unforgeableAdv (_sigAlg : SignatureAlg spec em M PK SK S) :=
  SecAdv (spec ++ₒ (M →ₒ S)) PK (M × S)

def unforgeableExp {sigAlg : SignatureAlg spec em M PK SK S}
    (adv : unforgeableAdv sigAlg) : SecExp spec em where
  main := do
    let (pk, sk) ← sigAlg.keygen
    let adv_so : QueryImpl (spec ++ₒ (M →ₒ S)) (StateT (M →ₒ S).QueryLog _) :=
      idOracle (spec := spec) ++ₛₒ sigAlg.signingOracle pk sk
    let ((m, σ), log) ← (simulateQ adv_so (adv.run pk)).run []
    let b ← sigAlg.verify pk m σ
    guard (!(log.wasQueried () m) && b)
  __ := sigAlg

end unforgeable

end SignatureAlg
