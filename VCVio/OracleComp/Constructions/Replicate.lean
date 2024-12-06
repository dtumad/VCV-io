/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.DistSemantics.Seq
import VCVio.OracleComp.DistSemantics.List
import Init.Data.Vector.Lemmas

/-!
# Running a Computation Multiple Times

This file defines a function `replicate oa n` that runs the computation `oa` a total of `n` times,
returning the result as a list of length `n`.

Note that while the executions are independent, they may no longer be after calling `simulate`.
-/


open OracleSpec Vector

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- Run the computation `oa` repeatedly `n` times to get a vector of `n` results. -/
def replicate {ι : Type} {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp spec α) : (n : ℕ) → OracleComp spec (Vector α n)
  | 0 => pure #v[]
  | n + 1 => push <$> oa <*> replicate oa n

def replicate_general {ι : Type} {spec : OracleSpec ι} {α : Type} (oa : OracleComp spec α)
    (Cont : ℕ → Type) (empty : Cont 0) (comb : {n : ℕ} → α → Cont n → Cont (n + 1))
    (n : ℕ) : OracleComp spec (Cont n) := match n with
  | 0 => pure empty
  | n + 1 => comb <$> oa <*> replicate_general oa Cont empty comb n

def replicate_list {ι : Type} {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp spec α) : (n : ℕ) → OracleComp spec (List α)
  | 0 => pure []
  | n + 1 => List.cons <$> oa <*> replicate_list oa n

-- TODO: this is probably the right way to be doing this
def replicate_for {ι : Type} {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp spec α) (n : ℕ) : OracleComp spec (List α) := do
  let mut xs := []
  for _ in List.finRange n do
    let x ← oa
    xs := x :: xs
  return xs

lemma probOutput_replicate_for {ι : Type} {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp spec α) (n : ℕ) (xs : List α) (h : xs.length = n) :
    [= xs | replicate_for oa n] = (xs.map ([= · | oa])).prod := by
  revert xs
  rw [replicate_for]
  simp only [bind_pure_comp, map_pure, List.forIn_yield_eq_foldlM, List.foldlM_range, bind_pure]
  induction n with
  | zero => {
      simp
  }
  | succ n hn => {
    intro xs hxs
    -- have := hxs
    -- rw [← List.length_reverse] at hxs
    have : xs.reverse.length = n + 1 := List.length_reverse xs ▸ hxs
    have h := List.exists_cons_of_length_eq_add_one this
    simp_rw [List.reverse_eq_cons_iff] at h
    obtain ⟨x, xs, rfl⟩ := h
    have : xs.length = n := by simpa using hxs
    specialize hn xs this
    -- rw [← List.prod_reverse, ← List.map_reverse, List.reverse_cons]
    rw [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
      List.map_reverse, List.prod_reverse,
      ← hn]
    simp [Fin.foldlM_succ]
    sorry
  }

variable (oa : OracleComp spec α)

@[simp]
lemma replicate_zero : oa.replicate 0 = pure #v[] := rfl

@[simp]
lemma replicate_succ (n : ℕ) : oa.replicate (n + 1) = push <$> oa <*> replicate oa n := rfl

/-- Repeating a specific value just returns a list of that element repeated. -/
lemma replicate_pure (x : α) (n : ℕ) :
    (pure x : OracleComp spec α).replicate n = pure (ofFn (Function.const _ x)) := by
  induction n with
  | zero => rfl
  | succ n hn => {
      simp [pure_seq, hn]
      apply Vector.toArray_inj
      simp [Vector.push, Vector.ofFn]
      ext x
      simp only [Array.size_push, Array.size_ofFn]
      rw [Array.getElem_push]
      simp only [Array.size_ofFn, Array.getElem_ofFn, Function.const_apply, dite_eq_ite, ite_self]
  }

section zero_add

/-- Running a computation `0 + n` times is the same as running it `n` times.
Because `0 + n` and `n` are not definitionally equal, regular equality will not typecheck. -/
lemma replicate_zero_add_heq (n : ℕ) : HEq (oa.replicate (0 + n)) (oa.replicate n) := by
  cases h : 0 + n <;> {rw [zero_add] at h; cases h; rfl}

/-- Running a computation `0 + n` times is the same as running it `n` times.
Requires substituting the equality between the two to properly typecheck the vector types. -/
lemma replicate_zero_add (n : ℕ) : oa.replicate (0 + n) = (zero_add n).symm ▸ oa.replicate n :=
  eq_of_heq <| (replicate_zero_add_heq oa n).trans <| heq_eqRec_iff_heq.2 HEq.rfl

lemma support_replicate_zero_add_heq (n : ℕ) :
    HEq (oa.replicate (0 + n)).support (oa.replicate n).support := by
  cases h : 0 + n <;> {rw [zero_add] at h; cases h; rfl}

lemma support_replicate_zero_add (n : ℕ) : (oa.replicate (0 + n)).support =
    (zero_add n).symm ▸ (oa.replicate n).support :=
  eq_of_heq <| heq_eqRec_iff_heq.2 (support_replicate_zero_add_heq oa n)

-- TODO: update with heq proofs
lemma finSupport_replicate_zero_add_heq (n : ℕ) [DecidableEq α]:
    HEq (oa.replicate (0 + n)).finSupport (oa.replicate n).finSupport := by
  cases h : 0 + n <;> {rw [zero_add] at h; cases h; rfl}

lemma finSupport_replicate_zero_add (n : ℕ) [DecidableEq α] :
    (oa.replicate (0 + n)).finSupport = (zero_add n).symm ▸ (oa.replicate n).finSupport :=
  eq_of_heq <| (finSupport_replicate_zero_add_heq oa n).trans <| heq_eqRec_iff_heq.2 HEq.rfl

lemma evalDist_replicate_zero_add_heq (n : ℕ) :
    HEq (evalDist (oa.replicate (0 + n))) (evalDist (oa.replicate n)) := by
  cases h : 0 + n <;> {rw [zero_add] at h; cases h; rfl}

lemma evalDist_replicate_zero_add (n : ℕ) :
    evalDist (oa.replicate (0 + n)) = (zero_add n).symm ▸ evalDist (oa.replicate n) :=
  eq_of_heq <| (evalDist_replicate_zero_add_heq oa n).trans <| heq_eqRec_iff_heq.2 HEq.rfl

@[simp]
lemma probOutput_replicate_zero_add (n : ℕ) (xs : Vector α (0 + n)) :
    -- let hxs : xs.1.length = n := (Vector.length_val xs).trans (zero_add n)
    [= xs | oa.replicate (0 + n)] = [= zero_add n ▸ xs | oa.replicate n] := by
  have h : [= xs | oa.replicate (0 + n)] = [= (zero_add n).symm ▸ xs | oa.replicate n] :=
  by congr <;> simp
  refine h.trans ?_
  congr

-- -- @[simp] TODO: should we simp this with the `subst` there?
-- lemma probEvent_replicate_zero_add (n : ℕ) (xss : (Mathlib.Vector α (0 + n)) → Prop)
--     [DecidablePred xss] :
--     [xss | oa.replicate (0 + n)] = [(zero_add n).symm ▸ xss | oa.replicate n] := by
--   congr <;> simp

end zero_add

section comm

/-- Running a computation `n + m` times is the same as running it `n` times then `m` times.
Because `n + m` and `m + n` are not definitionally equal, regular equality will not typecheck. -/
lemma replicate_add_comm_heq (n m : ℕ) : HEq (oa.replicate (n + m)) (oa.replicate (m + n)) := by
  cases h : n + m
  · cases h' : m + n
    · exact HEq.rfl
    · rw [add_comm n m, h'] at h
      exact (Nat.succ_ne_zero _ h).elim
  · cases h' : m + n
    · rw [add_comm m n, h] at h'
      exact (Nat.succ_ne_zero _ h').elim
    · rw [add_comm n m, h', Nat.add_one_inj] at h
      cases h
      rfl

lemma replicate_add_comm (n m : ℕ) :
    oa.replicate (n + m) = add_comm n m ▸ oa.replicate (m + n) := by
  refine eq_of_heq <| (replicate_add_comm_heq oa n m).trans <| heq_eqRec_iff_heq.2 HEq.rfl

end comm


-- lemma probFailure_seq_map (oa : OracleComp spec α) (ob : OracleComp spec β) (f : α → β → γ) :
--     [⊥ | f <$> oa <*> ob] = [⊥ | oa] + (1 - [⊥ | oa]) * [⊥ | ob] := by
--   -- rw [probFailure_seq_map]
--   sorry



@[simp]
lemma probFailure_replicate (oa : OracleComp spec α) (n : ℕ) :
    [⊥ | replicate oa n] = 1 - (1 - [⊥ | replicate oa n]) ^ n := by
  induction n with
  | zero => simp only [replicate_zero, probFailure_pure, tsub_zero, pow_zero, tsub_self]
  | succ n hn => {
      sorry
  }

/-- The probability of getting a vector from `replicate` is the product of the chances of
getting each of the individual elements. -/
@[simp]
lemma probOutput_replicate (oa : OracleComp spec α) (n : ℕ) (xs : Vector α n) :
    [= xs | replicate oa n] = (xs.toList.map ([= · | oa])).prod := by
  induction xs using Vector.elimAsList with
  | mk xs hxs => match xs with
    | [] => {
      sorry
    }
    | x :: xs => sorry

@[simp]
lemma support_replicate (oa : OracleComp spec α) (n : ℕ) :
    (replicate oa n).support = {xs | ∀ x ∈ xs.toList, x ∈ oa.support} := by
  refine Set.ext (λ xs ↦ ?_)
  rw [← probOutput_pos_iff, probOutput_replicate]
  simp only [CanonicallyOrderedCommSemiring.list_prod_pos, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, probOutput_pos_iff, Set.mem_setOf_eq]

-- @[simp] TODO: decidablility of this pred should be inferred from something else?
lemma support_replicate' (oa : OracleComp spec α) [DecidablePred (· ∈ oa.support)] (n : ℕ) :
    (replicate oa n).support = {xs | xs.toList.all (· ∈ oa.support)} := by
  refine Set.ext (λ xs ↦ ?_)
  rw [← probOutput_pos_iff, probOutput_replicate]
  simp only [CanonicallyOrderedCommSemiring.list_prod_pos, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, probOutput_pos_iff, List.all_eq_true, decide_eq_true_eq,
    Set.mem_setOf_eq]

section SelectableTypeVector

/-- Vectors can be selected uniformly if the underlying type can be.
Note: this isn't very efficient as an actual implementation in practice. -/
instance (α : Type) [Fintype α] [Inhabited α] [SelectableType α] (n : ℕ) :
    SelectableType (Vector α n) where
  selectElem := replicate ($ᵗ α) n
  probOutput_selectElem_eq xs ys := by simp

end SelectableTypeVector

end OracleComp
