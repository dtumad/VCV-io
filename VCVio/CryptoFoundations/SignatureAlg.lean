/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.SimSemantics.QueryTracking.LoggingOracle
import VCVio.OracleComp.Coercions.Append

/-!
# Asymmetric Encryption Schemes.

This file defines a type `AsymmEncAlg spec σ M PK SK C` to represent an protocol
for asymmetric encryption using oracles in `spec`, with message space `M`,
public/secret keys `PK` and `SK`, and ciphertext space `C`.
-/

open OracleSpec OracleComp

/-- Signature algorithm with access to oracles in `spec` (simulated with state `σ`),
where `M` is the space of messages, `PK`/`SK` are the spaces of the public/private keys,
and `S` is the type of the final signature. -/
structure SignatureAlg {ι : Type} (spec : OracleSpec ι)
    (σ M PK SK S : Type) extends OracleImpl spec σ where
  keygen : OracleComp spec (PK × SK)
  sign (pk : PK) (sk : SK) (m : M) : OracleComp spec S
  verify (pk : PK) (m : M) (s : S) : OracleComp spec Bool

namespace SignatureAlg

variable {ι : Type} {spec : OracleSpec ι} {σ M PK SK S : Type}

section sound

/-- Experiment to check that valid signatures succeed at being verified. -/
def soundnessExp (sigAlg : SignatureAlg spec σ M PK SK S)
    (m : M) : SecExp spec σ where
  main := do
    let (pk, sk) ← sigAlg.keygen
    let sig ← sigAlg.sign pk sk m
    sigAlg.verify pk m sig
  __ := sigAlg

/-- A signature algorithm is complete if valid signatures always verify. -/
def IsComplete (sigAlg : SignatureAlg spec σ M PK SK S) : Prop :=
  ∀ m : M, (sigAlg.soundnessExp m).advantage = 1

end sound

section unforgeable

variable [DecidableEq ι] [Inhabited S] [Fintype S] [DecidableEq S] [DecidableEq M]

def signingOracle (sigAlg : SignatureAlg spec σ M PK SK S)
    (pk : PK) (sk : SK) : (M →ₒ S) →[QueryLog (M →ₒ S)]ₛₒ spec :=
  λ () m log ↦ do
    let σ ← sigAlg.sign pk sk m
    return (σ, log.logQuery m σ)

abbrev unforgeableAdv (_sigAlg : SignatureAlg spec σ M PK SK S) :=
  SecAdv (spec ++ₒ (M →ₒ S)) PK (M × S)

def unforgeableExp {sigAlg : SignatureAlg spec σ M PK SK S}
    (adv : unforgeableAdv sigAlg) : SecExp spec σ where
  main := do
    let (pk, sk) ← sigAlg.keygen
    let adv_so := (sigAlg.signingOracle pk sk).liftRight
    let ((m, σ), log) ← simulate adv_so ∅ (adv.run pk)
    let b ← sigAlg.verify pk m σ
    return b && !(log.wasQueried () m)
  __ := sigAlg

end unforgeable

end SignatureAlg
