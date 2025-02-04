/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.IsTracking
import VCVio.OracleComp.RunIO

/-!
# Logging Queries Made by a Computation

-/

universe u v w

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α β : Type}

namespace OracleSpec

/-- Log of oracle queries represented by lists of input output pairs,
parameterized by the set of oracles available. -/
def QueryLog (spec : OracleSpec ι) : Type :=
  (i : ι) → List (spec.domain i × spec.range i)

-- Better repr but maybe not better in general
def QueryLog' (spec : OracleSpec ι) : Type :=
  List (Σ i : ι, spec.domain i × spec.range i)

namespace QueryLog

instance : EmptyCollection (QueryLog spec) := ⟨λ _ ↦ []⟩
instance : Append (QueryLog spec) := ⟨λ log log' i ↦ (log i) ++ (log' i)⟩
instance : Monoid (QueryLog spec) where
  mul := instAppend.append
  one := instEmptyCollection.emptyCollection
  mul_assoc := fun a b c => by sorry
  one_mul := sorry
  mul_one := sorry

end QueryLog

instance : EmptyCollection (QueryLog' spec) := ⟨[]⟩
instance : Append (QueryLog' spec) := ⟨List.append⟩

namespace QueryLog

section logQuery

/-- Update a query log by adding a new element to the appropriate list.
Note that this requires decidable equality on the indexing set. -/
def logQuery (log : QueryLog spec) {i : ι}
    (t : spec.domain i) (u : spec.range i) : QueryLog spec :=
  Function.update log i ((t, u) :: log i)

end logQuery

def singleton {i : ι} (t : spec.domain i) (u : spec.range i) : QueryLog spec :=
  Function.update (λ _ ↦ []) i [(t, u)]

/-- Check if an element was ever queried in a log of queries.
Relies on decidable equality of the domain types of oracles. -/
def wasQueried [spec.DecidableEq] (log : QueryLog spec) (i : ι) (t : spec.domain i) : Bool :=
  match (log i).find? (λ (t', _) ↦ t = t') with
  | Option.some _ => true
  | Option.none => false

end QueryLog

def QueryLog'.singleton {i : ι} (t : spec.domain i) (u : spec.range i) : QueryLog' spec :=
  [⟨i, (t, u)⟩]

end OracleSpec

open OracleComp OracleSpec

def loggingOracleNew : SimOracle' spec spec (WriterT (QueryLog spec)) where
  impl | query i t => do
    let u ← query i t
    tell (QueryLog.singleton t u)
    return u

def loggingOracle' : SimOracle' spec spec (WriterT (QueryLog' spec)) where
  impl | query i t => do
    let u ← query i t
    tell (QueryLog'.singleton t u)
    return u

def logingOracle'' : QueryImpl spec (WriterT (QueryLog' spec) (OracleComp spec)) where
  impl | query i t => do
    let u ← query i t
    tell (QueryLog'.singleton t u)
    return u

-- `(22, [⟨20, ((), 8)⟩, ⟨20, ((), 14)⟩])`
-- `(9, [⟨20, ((), 6)⟩, ⟨20, ((), 3)⟩])`
#eval OracleComp.runIO (simulateT' loggingOracle' (do
    (Nat.add) <$> $[0..20] <*> $[0..20])).run

/-- Simulation oracle for tracking the quries in a `QueryLog`, without modifying the actual
behavior of the oracle. Requires decidable equality of the indexing set to determine
which list to update when queries come in. -/
def loggingOracle : SimOracle spec spec (QueryLog spec) where
  impl | query i t => do
    let u ← query i t
    modifyGet λ log ↦ (u, log.logQuery t u)

namespace loggingOracle

@[simp]
lemma apply_eq (q : OracleQuery spec α) : loggingOracle.impl q =
    match q with | query i t => (do
      let u ← query i t
      modifyGet λ log ↦ (u, log.logQuery t u)) := rfl

instance : (loggingOracle (spec := spec)).IsTracking where
  state_indep | query _ _, _ => rfl

end loggingOracle
