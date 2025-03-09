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

/-- Dummy `Monoid` instance to be used with `WriterT`. Actual constructions should use `append`. -/
instance : Monoid (QueryLog spec) where
  mul := List.append
  mul_assoc := List.append_assoc
  one := List.nil
  one_mul := List.nil_append
  mul_one := List.append_nil

@[simp] -- Automatically reduce "multiplication" of query logs to `List.append`
lemma monoid_mul_def (qc qc' : QueryLog spec) :
  (@HMul.hMul _ _ _ (@instHMul _ (Monoid.toMulOneClass.toMul)) qc qc')
     = (qc : List _) ++ (qc' : List _) := rfl

/-- Query log with a single entry. Note that we do pattern matching here to simplify `loggingOracle`.-/
def singleton (q : OracleQuery spec α) (u : α) : QueryLog spec :=
  match q with | query i t => [⟨i, (t, u)⟩]

/-- Update a query log by adding a new element to the appropriate list.
Note that this requires decidable equality on the indexing set. -/
def logQuery (log : QueryLog spec) (q : OracleQuery spec α) (u : α) :
    QueryLog spec := log ++ singleton q u

instance [DecidableEq ι] [spec.DecidableEq] : DecidableEq (QueryLog spec) :=
  inferInstanceAs (DecidableEq (List _))

section getQ

variable [DecidableEq ι]

/-- Get all the queries made to oracle `i`. -/
def getQ  (log : QueryLog spec) (i : ι) : List (spec.domain i × spec.range i) :=
  List.foldr (fun ⟨j, t, u⟩ xs => if h : j = i then h ▸ (t, u) :: xs else xs) [] log

-- NOTE: should this simp? feels bad to simp with ▸ and pattern matching in target
lemma getQ_singleton (q : OracleQuery spec α) (u : α) (i : ι) :
    getQ (singleton q u) i = match q with
      | query j t => if h : j = i then [h ▸ (t, u)] else [] := by
  cases q with | query i t => ?_
  simp [getQ, singleton]

@[simp]
lemma getQ_singleton_self (i : ι) (t : spec.domain i) (u : spec.range i) :
    getQ (singleton (query i t) u) i = [(t, u)] := by simp [getQ_singleton]

lemma getQ_singleton_of_ne {q : OracleQuery spec α} {u : α} {i : ι}
    (h : q.index ≠ i) : getQ (singleton q u) i = [] := by
  cases q with | query i t => simpa [getQ_singleton] using h

@[simp]
lemma getQ_append (log log' : QueryLog spec) (i : ι) :
    (log ++ log').getQ i = log.getQ i ++ log'.getQ i := sorry

@[simp]
lemma getQ_logQuery (log : QueryLog spec) (q : OracleQuery spec α) (u : α)
    (i : ι) : (log.logQuery q u).getQ i = log.getQ i ++ (singleton q u).getQ i := by
  rw [logQuery, getQ_append]

end getQ

section countQ

variable [DecidableEq ι]

def countQ (log : QueryLog spec) (i : ι) : ℕ := (log.getQ i).length

@[simp]
lemma countQ_singleton (q : OracleQuery spec α) (u : α) (i : ι) :
    countQ (singleton q u) i = if q.index = i then 1 else 0 := by
  cases q with | query i t => ?_
  simp only [countQ, getQ_singleton, OracleQuery.index_query]
  split_ifs with hi <;> rfl

lemma countQ_singleton_self (i : ι) (t : spec.domain i) (u : spec.range i) :
    countQ (singleton (query i t) u) i = 1 := by simp

@[simp]
lemma countQ_append (log log' : QueryLog spec) (i : ι) :
    (log ++ log').countQ i = log.countQ i + log'.countQ i := by simp [countQ]

@[simp]
lemma countQ_logQuery (log : QueryLog spec) (q : OracleQuery spec α) (u : α)
    (i : ι) : (log.logQuery q u).countQ i = log.countQ i + if q.index = i then 1 else 0 := by
  rw [logQuery, countQ_append, countQ_singleton]

end countQ

section wasQueried

/-- Check if an element was ever queried in a log of queries.
Relies on decidable equality of the domain types of oracles. -/
def wasQueried [DecidableEq ι] [spec.DecidableEq] (log : QueryLog spec)
    (i : ι) (t : spec.domain i) : Bool :=
  match (log.getQ i).find? (λ (t', _) ↦ t = t') with
  | Option.some _ => true
  | Option.none => false

end wasQueried

section prod

variable {ι₁ ι₂ : Type*} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

/-- Get only the portion of the log for queries in `spec₁`. -/
protected def take_fst (log : QueryLog (spec₁ ++ₒ spec₂)) : QueryLog spec₁ :=
  log.filterMap (fun | ⟨.inl i, t, u⟩ => some ⟨i, t, u⟩ | _ => none)

/-- Get only the portion of the log for queries in `spec₂`. -/
protected def take_snd (log : QueryLog (spec₁ ++ₒ spec₂)) : QueryLog spec₂ :=
  log.filterMap (fun | ⟨.inr i, t, u⟩ => some ⟨i, t, u⟩ | _ => none)

/-- View a log for `spec₁` as one for `spec₁ ++ₒ spec₂` by inclusion. -/
protected def lift_inl (log : QueryLog spec₁) : QueryLog (spec₁ ++ₒ spec₂) :=
  log.map fun ⟨i, t, u⟩ => ⟨.inl i, t, u⟩

/-- View a log for `spec₂` as one for `spec₁ ++ₒ spec₂` by inclusion. -/
protected def lift_inr (log : QueryLog spec₂) : QueryLog (spec₁ ++ₒ spec₂) :=
  log.map fun ⟨i, t, u⟩ => ⟨.inr i, t, u⟩

instance : Coe (QueryLog spec₁) (QueryLog (spec₁ ++ₒ spec₂)) := ⟨QueryLog.lift_inl⟩
instance : Coe (QueryLog spec₂) (QueryLog (spec₁ ++ₒ spec₂)) := ⟨QueryLog.lift_inr⟩

end prod

end QueryLog

end OracleSpec

open Prod OracleSpec OracleComp

/-- Simulation oracle for tracking the quries in a `QueryLog`, without modifying the actual
behavior of the oracle. Requires decidable equality of the indexing set to determine
which list to update when queries come in.

Note that the need to do pattern matching on `q` -/
def loggingOracle {ι : Type u} {spec : OracleSpec ι} :
    QueryImpl spec (WriterT (QueryLog spec) (OracleComp spec)) where
  impl q := do let u ← q; tell (QueryLog.singleton q u); return u

namespace loggingOracle

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type u}

@[simp]
lemma apply_eq (q : OracleQuery spec α) : loggingOracle.impl q =
    do let u ← q; tell (QueryLog.singleton q u); return u := rfl

@[simp]
lemma fst_map_run_simulateQ (oa : OracleComp spec α) :
    (fst <$> (simulateQ loggingOracle oa).run) = oa :=
  fst_map_writerT_run_simulateQ (by simp) oa

@[simp]
lemma run_simulateQ_bind_fst (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    ((simulateQ loggingOracle oa).run >>= fun x => ob x.1) = oa >>= ob := by
  rw [← bind_map_left fst, fst_map_run_simulateQ]

@[simp]
lemma probFailure_run_simulateQ [spec.FiniteRange] (oa : OracleComp spec α) :
    [⊥ | (simulateQ loggingOracle oa).run] = [⊥ | oa] :=
  probFailure_writerT_run_simulateQ (by simp) (by simp) oa

@[simp]
lemma noFailure_run_simulateQ_iff (oa : OracleComp spec α) :
    noFailure (simulateQ loggingOracle oa).run ↔ noFailure oa :=
  noFailure_writerT_run_simulateQ_iff (by simp) (by simp) oa

instance noFailure_simulateQ (oa : OracleComp spec α) [noFailure oa] :
    noFailure (simulateQ loggingOracle oa).run := by
  rwa [noFailure_run_simulateQ_iff]

end loggingOracle
