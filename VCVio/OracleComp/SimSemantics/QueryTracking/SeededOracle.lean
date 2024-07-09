/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate

/-!
# Seeding Results of Queries

This file defines a simulation oracle `seededOracle` for pre-choosing the responses to queries.
The internal state is a list of seeded values for each oracle, and the simulation will use these
when possible, defaulting back to the original behavior if the seed doesn't have enough values.

We also clear the remaining seed if any single oracle fails to have enough seed values.
This simplifies a number of lemmas by making the computation revert to its original behavior.
-/

open OracleComp OracleSpec BigOperators

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}

namespace OracleSpec

/-- Type to represent a store of seed values to use in a computation, represented as a function.
Updates to individual seed lists are performed via continuation passing. -/
def QuerySeed (spec : OracleSpec ι) : Type :=
  (i : ι) → List (spec.range i)

namespace QuerySeed

instance : EmptyCollection (QuerySeed spec) := ⟨λ _ ↦ []⟩

/-- Add a list of values to the query seed.-/
def addValues (seed : QuerySeed spec) {i : ι} (us : List (spec.range i)) : QuerySeed spec :=
  Function.update seed i (seed i ++ us)

/-- Add a single value into the seed, by adding a singleton list -/
def addValue (seed : QuerySeed spec) {i : ι} (u : spec.range i) : QuerySeed spec :=
  seed.addValues [u]

/-- Take only the first `n` values of the seed at index `i`. -/
def takeAtIndex (seed : QuerySeed spec) (i : ι) (n : ℕ) : QuerySeed spec :=
  Function.update seed i ((seed i).take n)

end QuerySeed

end OracleSpec

def seededOracle [DecidableEq ι] : spec →[QuerySeed spec]ₛₒ spec :=
  λ i t seed ↦ match seed i with
    | u :: us => return (u, Function.update seed i us)
    | [] => (·, ∅) <$> query i t

namespace seededOracle

end seededOracle
