/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Append

/-!
# Distinguishers for Query Implementations

This file defines the type `QueryImpl.Distinguisher spec` of distinguishers for a
pair of oracle implementations, as a computation returning a `Bool` with those oracles.
`DistinguisherExperiment` runs one on a pair of computations.

We also define a predicate `DistinguisherBound` to specify a bound on the chance of success.
-/

open OracleComp OracleSpec

variable {ι : Type _} {spec : OracleSpec ι} {α β γ : Type _}

namespace QueryImpl

protected def Distinguisher (α _β : Type _) (spec : OracleSpec ι) :=
  α → OracleComp (unifSpec ++ₒ spec) Bool

def Distinguisher.DistinguisherExp (adversary : QueryImpl.Distinguisher α β spec)
    (gen : ProbComp (α × β))
    (impl₁ impl₂ : α × β → QueryImpl spec ProbComp) :
    ProbComp Unit := do
  let b ←$ᵗ Bool
  let impl := if b then impl₁ else impl₂
  let x ← gen
  let b' ← simulateQ (idOracle ++ₛₒ impl x) (adversary x.1)
  guard (b = b')

noncomputable def Distinguisher.advantage (adversary : QueryImpl.Distinguisher α β spec)
    (gen : ProbComp (α × β))
    (impl₁ impl₂ : α × β → QueryImpl spec ProbComp) :=
  [= () | adversary.DistinguisherExp gen impl₁ impl₂]

end QueryImpl
