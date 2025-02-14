/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.IsTracking
import VCVio.OracleComp.RunIO
import VCVio.OracleComp.Coercions.SimOracle
import ToMathlib.Control.WriterT

/-!
# Logging Queries Made by a Computation

-/

universe u v w

namespace OracleSpec

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type v}

/-- Log of oracle queries represented by lists of input output pairs,
parameterized by the set of oracles available. -/
@[reducible]
def QueryLog (spec : OracleSpec ι) : Type _ :=
  List ((i : ι) × spec.domain i × spec.range i)

namespace QueryLog

instance : Append (QueryLog spec) := ⟨List.append⟩
instance : Monoid (QueryLog spec) where
  mul := List.append
  mul_assoc := List.append_assoc
  one := List.nil
  one_mul := List.nil_append
  mul_one := List.append_nil

/-- Get all the queries made to oracle `i`. -/
def getQ [DecidableEq ι] (log : QueryLog spec) (i : ι) :
    List (spec.domain i × spec.range i) :=
  log.foldr (fun ⟨j, t, u⟩ xs => if h : j = i then h ▸ (t, u) :: xs else xs) []

def countQ [DecidableEq ι] (log : QueryLog spec) (i : ι) : ℕ :=
  (log.getQ i).length

instance [DecidableEq ι] [spec.DecidableEq] : DecidableEq (QueryLog spec) :=
  inferInstanceAs (DecidableEq (List _))

def singleton {i : ι} (t : spec.domain i) (u : spec.range i) :
    QueryLog spec := [⟨i, (t, u)⟩]

/-- Update a query log by adding a new element to the appropriate list.
Note that this requires decidable equality on the indexing set. -/
def logQuery (log : QueryLog spec) {i : ι} (t : spec.domain i) (u : spec.range i) :
    QueryLog spec := log ++ singleton t u

/-- Check if an element was ever queried in a log of queries.
Relies on decidable equality of the domain types of oracles. -/
def wasQueried [DecidableEq ι] [spec.DecidableEq] (log : QueryLog spec)
    (i : ι) (t : spec.domain i) : Bool :=
  match (log.getQ i).find? (λ (t', _) ↦ t = t') with
  | Option.some _ => true
  | Option.none => false

variable {ι₁ ι₂ : Type*} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

def fst (log : QueryLog (spec₁ ++ₒ spec₂)) : QueryLog spec₁ :=
  log.filterMap (fun ⟨i, t, u⟩ ↦ match i with | .inl i => some (⟨i, t, u⟩) | .inr _ => none)

def snd (log : QueryLog (spec₁ ++ₒ spec₂)) : QueryLog spec₂ :=
  log.filterMap (fun ⟨i, t, u⟩ ↦ match i with | .inl _ => none | .inr i => some (⟨i, t, u⟩))

def inl (log : QueryLog spec₁) : QueryLog (spec₁ ++ₒ spec₂) :=
  log.map (fun ⟨i, t, u⟩ ↦ ⟨.inl i, t, u⟩)

def inr (log : QueryLog spec₂) : QueryLog (spec₁ ++ₒ spec₂) :=
  log.map (fun ⟨i, t, u⟩ ↦ ⟨.inr i, t, u⟩)

instance : Coe (QueryLog spec₁) (QueryLog (spec₁ ++ₒ spec₂)) := ⟨inl⟩
instance : Coe (QueryLog spec₂) (QueryLog (spec₁ ++ₒ spec₂)) := ⟨inr⟩

end QueryLog

end OracleSpec

open OracleSpec

/-- Simulation oracle for tracking the quries in a `QueryLog`, without modifying the actual
behavior of the oracle. Requires decidable equality of the indexing set to determine
which list to update when queries come in. -/
def loggingOracle {ι : Type u} {spec : OracleSpec ι} :
    QueryImpl spec (WriterT (QueryLog spec) (OracleComp spec)) where
  impl | query i t => do
    let u ← query i t
    tell (QueryLog.singleton t u)
    return u

namespace loggingOracle

variable {ι} {spec : OracleSpec ι} {α}

@[simp]
lemma apply_eq (q : OracleQuery spec α) :
  loggingOracle.impl q = match q with | query i t => do
    let u ← query i t
    tell (QueryLog.singleton t u)
    return u :=
  rfl

-- instance : (loggingOracle (spec := spec)).IsTracking where
--   state_indep | query _ _, _ => rfl

-- theorem simulate_eq_append_simulate_empty [spec.DecidableEq] (oa : OracleComp spec α)
--     (log : QueryLog spec) :
--       simulate loggingOracle log oa = do
--         let ⟨a, log_oa⟩ ← simulate loggingOracle ∅ oa
--         return (a, log.append log_oa) := by
--   induction oa using OracleComp.induction with
--   | pure a => simp [simulate_pure]; ext : 1; simp [QueryLog.append]
--   | query_bind i t oa ih => simp [simulate_bind, ih]; sorry
--   | failure => simp

-- variable [spec₁.DecidableEq] [spec₂.DecidableEq]
--   [DecidableEq ι₁] [DecidableEq ι₂]

-- -- Should this be `simp`?
-- theorem inl_eq (oa : OracleComp spec₁ α) (log : QueryLog (spec₁ ++ₒ spec₂)) :
--   simulate (loggingOracle (spec := spec₁ ++ₒ spec₂)) log oa = do
--     let ⟨a, log_oa⟩ ← simulate (loggingOracle (spec := spec₁)) ∅ oa
--     return (a, log.append (QueryLog.inl log_oa)) := by
--   simp [liftM_eq_liftComp, bind_pure_comp]
--   sorry

-- theorem inr_eq (oa : OracleComp spec₂ α) (log : QueryLog (spec₁ ++ₒ spec₂)) :
--   simulate (loggingOracle (spec := spec₁ ++ₒ spec₂)) log oa = do
--     let ⟨a, log_oa⟩ ← simulate (loggingOracle (spec := spec₂)) ∅ oa
--     return (a, log.append (QueryLog.inr log_oa)) := by
--   simp [liftM_eq_liftComp, bind_pure_comp]
--   sorry

end loggingOracle

#eval! (OracleComp.simulateQ loggingOracle
  (for i in List.range 50 do let _ ← $[0..i])).run
