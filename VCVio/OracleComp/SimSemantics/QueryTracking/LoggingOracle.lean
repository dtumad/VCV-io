/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.IsTracking
import VCVio.OracleComp.Coercions.SimOracle

/-!
# Logging Queries Made by a Computation

-/

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

namespace OracleSpec

/-- Log of oracle queries represented by lists of input output pairs,
parameterized by the set of oracles available. -/
def QueryLog (spec : OracleSpec ι) : Type :=
  (i : ι) → List (spec.domain i × spec.range i)

instance : EmptyCollection (QueryLog spec) := ⟨λ _ ↦ []⟩

-- instance [spec.DecidableEq] : DecidableEq (QueryLog spec) where
--   decide x y := by sorry

namespace QueryLog

@[ext]
theorem ext (log₁ log₂ : QueryLog spec) (h : ∀ i, log₁ i = log₂ i) : log₁ = log₂ := by
  unfold QueryLog
  ext i : 1
  exact h i

@[simp]
theorem emptyCollection_eq : (∅ : QueryLog spec) = λ _ ↦ [] := rfl

-- variable [DecidableEq ι₁] [DecidableEq ι₂]

section logQuery

/-- Update a query log by adding a new element to the appropriate list.
Note that this requires decidable equality on the indexing set. -/
def logQuery [DecidableEq ι] (log : QueryLog spec) {i : ι}
    (t : spec.domain i) (u : spec.range i) : QueryLog spec :=
  Function.update log i ((t, u) :: log i)

end logQuery

/-- Check if an element was ever queried in a log of queries.
Relies on decidable equality of the domain types of oracles. -/
def wasQueried [spec.DecidableEq] (log : QueryLog spec) (i : ι) (t : spec.domain i) : Bool :=
  match (log i).find? (λ (t', _) ↦ t = t') with
  | Option.some _ => true
  | Option.none => false

/-- Append two logs. Since the queries are pre-pended, the second log is added to the front of the
  first. -/
def append (log₁ : QueryLog spec) (log₂ : QueryLog spec) : QueryLog spec :=
  λ i ↦ log₂ i ++ log₁ i

def fst (log : QueryLog (spec₁ ++ₒ spec₂)) : QueryLog spec₁ :=
  λ i ↦ log (.inl i)
def snd (log : QueryLog (spec₁ ++ₒ spec₂)) : QueryLog spec₂ :=
  λ i ↦ log (.inr i)

def inl (log : QueryLog spec₁) : QueryLog (spec₁ ++ₒ spec₂)
  | .inl i => log i | .inr _ => []
def inr (log : QueryLog spec₂) : QueryLog (spec₁ ++ₒ spec₂)
  | .inl _ => [] | .inr i => log i

instance : Coe (QueryLog spec₁) (QueryLog (spec₁ ++ₒ spec₂)) := ⟨inl⟩
instance : Coe (QueryLog spec₂) (QueryLog (spec₁ ++ₒ spec₂)) := ⟨inr⟩

@[simp]
theorem append_apply (log₁ : QueryLog spec) (log₂ : QueryLog spec) (i : ι) :
  (log₁.append log₂) i = log₂ i ++ log₁ i := rfl

@[simp]
theorem append_empty (log : QueryLog spec) : log.append ∅ = log := by ext; simp [append]

@[simp]
theorem empty_append (log : QueryLog spec) : (∅ : QueryLog spec).append log = log := by
  ext; simp [append]

theorem append_assoc (log₁ : QueryLog spec) (log₂ : QueryLog spec) (log₃ : QueryLog spec) :
    (log₁.append log₂).append log₃ = log₁.append (log₂.append log₃) := by
  ext; simp [append]

end QueryLog

end OracleSpec

open OracleComp OracleSpec

variable [DecidableEq ι] [DecidableEq ι₁] [DecidableEq ι₂]

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

theorem simulate_eq_append_simulate_empty [spec.DecidableEq] (oa : OracleComp spec α)
    (log : QueryLog spec) :
      simulate loggingOracle log oa = do
        let ⟨a, log_oa⟩ ← simulate loggingOracle ∅ oa
        return (a, log.append log_oa) := by
  induction oa using OracleComp.induction with
  | pure a => simp [simulate_pure]; ext : 1; simp [QueryLog.append]
  | query_bind i t oa ih => simp [simulate_bind, ih]; sorry
  | failure => simp

variable [spec₁.DecidableEq] [spec₂.DecidableEq]

-- Should this be `simp`?
theorem inl_eq (oa : OracleComp spec₁ α) (log : QueryLog (spec₁ ++ₒ spec₂)) :
  simulate (loggingOracle (spec := spec₁ ++ₒ spec₂)) log oa = do
    let ⟨a, log_oa⟩ ← simulate (loggingOracle (spec := spec₁)) ∅ oa
    return (a, log.append (QueryLog.inl log_oa)) := by
  simp [liftM_eq_liftComp, bind_pure_comp]
  sorry

theorem inr_eq (oa : OracleComp spec₂ α) (log : QueryLog (spec₁ ++ₒ spec₂)) :
  simulate (loggingOracle (spec := spec₁ ++ₒ spec₂)) log oa = do
    let ⟨a, log_oa⟩ ← simulate (loggingOracle (spec := spec₂)) ∅ oa
    return (a, log.append (QueryLog.inr log_oa)) := by
  simp [liftM_eq_liftComp, bind_pure_comp]
  sorry

end loggingOracle
