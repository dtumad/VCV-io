/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Transformers.WriterT

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

-- variable {ι₁ ι₂ : Type*} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

-- def fst (log : QueryLog (spec₁ ++ₒ spec₂)) : QueryLog spec₁ :=
--   log.map sorry

-- def snd (log : QueryLog (spec₁ ++ₒ spec₂)) : QueryLog spec₂ :=
--   sorry --λ i ↦ log (.inr i)

-- def inl (log : QueryLog spec₁) : QueryLog (spec₁ ++ₒ spec₂)
--   | .inl i => log i | .inr _ => []
-- def inr (log : QueryLog spec₂) : QueryLog (spec₁ ++ₒ spec₂)
--   | .inl _ => [] | .inr i => log i

-- instance : Coe (QueryLog spec₁) (QueryLog (spec₁ ++ₒ spec₂)) := ⟨inl⟩
-- instance : Coe (QueryLog spec₂) (QueryLog (spec₁ ++ₒ spec₂)) := ⟨inr⟩

-- @[simp]
-- theorem append_apply (log₁ : QueryLog spec) (log₂ : QueryLog spec) (i : ι) :
--   (log₁.append log₂) i = log₂ i ++ log₁ i := rfl

-- @[simp]
-- theorem append_empty (log : QueryLog spec) : log.append ∅ = log := by ext; simp [append]

-- @[simp]
-- theorem empty_append (log : QueryLog spec) : (∅ : QueryLog spec).append log = log := by
--   ext; simp [append]

-- theorem append_assoc (log₁ : QueryLog spec) (log₂ : QueryLog spec) (log₃ : QueryLog spec) :
--     (log₁.append log₂).append log₃ = log₁.append (log₂.append log₃) := by
--   ext; simp [append]

end QueryLog

end OracleSpec

open Prod OracleSpec OracleComp

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

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type u}

@[simp]
lemma apply_eq (q : OracleQuery spec α) : loggingOracle.impl q =
    match q with | query i t => do
      let u ← query i t
      tell (QueryLog.singleton t u)
      return u := rfl

@[simp]
lemma fst_map_run_simulateQ (oa : OracleComp spec α) :
    (fst <$> (simulateQ loggingOracle oa).run) = oa :=
  fst_map_writerT_run_simulateQ (fun (query i t) => by simp) oa

@[simp]
lemma run_simulateQ_bind_fst (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    ((simulateQ loggingOracle oa).run >>= fun x => ob x.1) = oa >>= ob := by
  rw [← bind_map_left fst, fst_map_run_simulateQ]

@[simp]
lemma probFailure_run_simulateQ [spec.FiniteRange] (oa : OracleComp spec α) :
    [⊥ | (simulateQ loggingOracle oa).run] = [⊥ | oa] :=
  probFailure_writerT_run_simulateQ (fun (query i t) => by simp) (fun (query i t) => by simp) oa

@[simp]
lemma noFailure_run_simulateQ_iff (oa : OracleComp spec α) :
    noFailure (simulateQ loggingOracle oa).run ↔ noFailure oa := by
  sorry

instance noFailure_simulateQ (oa : OracleComp spec α) [noFailure oa] :
    noFailure (simulateQ loggingOracle oa).run := by sorry

end loggingOracle
