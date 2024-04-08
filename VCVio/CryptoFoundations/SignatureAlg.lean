/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.OracleSpec.Append
import VCVio.OracleComp.SimSemantics.QueryTracking.LoggingOracle

import VCVio.OracleComp.SimSemantics.QueryTracking.CachingOracle
import VCVio.OracleComp.SimSemantics.Append

/-!
# Asymmetric Encryption Schemes.

This file defines a type `AsymmEncAlg spec M PK SK C` to represent an protocol
for asymmetric encryption using oracles in `spec`, with message space `M`,
public/secret keys `PK` and `SK`, and ciphertext space `C`.
-/

open OracleSpec OracleComp

structure SignatureAlg (spec : OracleSpec)
    (M PK SK S : Type) extends OracleAlg spec where
  keygen : Unit → OracleComp spec (PK × SK)
  sign : PK → SK → M → OracleComp spec S
  verify : PK → M → S → OracleComp spec Bool


namespace SignatureAlg

variable {spec : OracleSpec}
    {M PK SK S : Type} [Inhabited S] [DecidableEq M] [DecidableEq S]
    [Fintype S]

def soundnessExp (sigAlg : SignatureAlg spec M PK SK S)
    (m : M) : SecExp spec (PK × SK) Bool where
  inpGen := sigAlg.keygen ()
  main := λ (pk, sk) ↦ do
    let σ ← sigAlg.sign pk sk m
    sigAlg.verify pk m σ
  isValid := λ _ b ↦ b = true
  __ := sigAlg

def unforgeableAdv (_sigAlg : SignatureAlg spec M PK SK S) :=
SecAdv (spec ++ (M →ₒ S)) PK (M × S)

def signingOracle (sigAlg : SignatureAlg spec M PK SK S)
    (pk : PK) (sk : SK) :
    (M →ₒ S) →[QueryLog (M →ₒ S)]ₛₒ spec :=
  λ () m log ↦ do
    let σ ← sigAlg.sign pk sk m
    return (σ, log.logQuery m σ)

def unforgeableExp {sigAlg : SignatureAlg spec M PK SK S}
    (adv : unforgeableAdv sigAlg) :
    SecExp spec (PK × SK) Bool where
  inpGen := sigAlg.keygen ()
  main := λ ⟨pk, sk⟩ ↦ do
    let ((m, σ), ((), log)) ←
      simulate (idOracle ++ₛₒ sigAlg.signingOracle pk sk)
        (adv.run pk) ((), λ _ ↦ [])
    let b ← sigAlg.verify pk m σ
    return (b && !(log.wasQueried () m))
  isValid := λ _ b ↦ b = true
  __ := sigAlg


end SignatureAlg