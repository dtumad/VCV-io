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

This file defines a type `AsymmEncAlg spec M PK SK C` to represent an protocol
for asymmetric encryption using oracles in `spec`, with message space `M`,
public/secret keys `PK` and `SK`, and ciphertext space `C`.
-/

open OracleSpec OracleComp BigOperators ENNReal

structure SignatureAlg' {ι : Type} (spec : OracleSpec ι)
    (σ M PK SK S : Type) extends OracleImpl spec σ where
  keygen : OracleComp spec (PK × SK)
  sign (pk : PK) (sk : SK) (m : M) : OracleComp spec S
  verify (pk : PK) (m : M) (s : S) : OracleComp spec Bool

structure SignatureAlg {ι : Type} (spec : ℕ → OracleSpec ι)
  (M PK SK S : ℕ → Type) extends OracleAlg spec where
  keygen (sp : ℕ) : OracleComp (unifSpec ++ₒ spec sp) (PK sp × SK sp)
  sign (sp : ℕ) : PK sp → SK sp → M sp → OracleComp (unifSpec ++ₒ spec sp) (S sp)
  verify (sp : ℕ) : PK sp → M sp → S sp → OracleComp (unifSpec ++ₒ spec sp) Bool

namespace SignatureAlg

variable {ι : Type} {spec : ℕ → OracleSpec ι} {M PK SK S : ℕ → Type}

section sound

def soundnessExp (sigAlg : SignatureAlg spec M PK SK S)
    (mDist : (sp : ℕ) → OracleComp (spec sp) (M sp)) :
    SecExp spec where
  main := λ sp ↦ do
    let m ← mDist sp
    let (pk, sk) ← sigAlg.keygen sp
    let σ ← sigAlg.sign sp pk sk m
    sigAlg.verify sp pk m σ
  __ := sigAlg

def isSound (sigAlg : SignatureAlg spec M PK SK S) : Prop :=
  ∀ mDist, negligible (1 - (soundnessExp sigAlg mDist).advantage)


end sound

section signingOracle

variable [Π sp, Inhabited (S sp)] [Π sp, DecidableEq (M sp)]
  [Π sp, DecidableEq (S sp)] [Π sp, Fintype (S sp)]

def signingOracle (sigAlg : SignatureAlg spec M PK SK S)
    (sp : ℕ) (pk : PK sp) (sk : SK sp) :
    (M sp →ₒ S sp) →[QueryLog (M sp →ₒ S sp)]ₛₒ unifSpec ++ₒ spec sp :=
  λ () m log ↦ do
    let σ ← sigAlg.sign sp pk sk m
    return (σ, log.logQuery m σ)

-- port

end signingOracle

section unforgeable

variable [Π sp, Inhabited (S sp)] [Π sp, DecidableEq (M sp)]
  [Π sp, DecidableEq (S sp)] [Π sp, Fintype (S sp)]
  [DecidableEq ι]

def unforgeableAdv (_sigAlg : SignatureAlg spec M PK SK S) :=
SecAdv (λ sp ↦ spec sp ++ₒ (M sp →ₒ S sp)) PK (λ sp ↦ M sp × S sp)

-- def unforgeableExp {sigAlg : SignatureAlg spec M PK SK S}
--     (adv : unforgeableAdv sigAlg) :
--     SecExp spec where
--   -- inpGen := sigAlg.keygen ()
--   main := λ sp ↦ do
--     let (pk, sk) ← sigAlg.keygen sp
--     let ((m, σ), ((), log)) ←
--       simulate (idOracle ++ₛₒ sigAlg.signingOracle sp pk sk)
--         ((), λ _ ↦ []) (adv.run sp pk)
--     let b ← sigAlg.verify sp pk m σ
--     return (b && !(log.wasQueried () m))
--   __ := sigAlg

end unforgeable

end SignatureAlg
