/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.Seq
import ToMathlib.General

/-!
# Distribution Semantics for Lists and Vectors

This file collects various lemmas about the monadic sequence operation `og <*> oa`.

One especially important case is `f <$> oa <*> ob` where `f : α → β → γ`,
that runs the two computations `oa` and `ob` to get some `x` and `y` respectively,
returning only the value `f x y`.
-/

open Mathlib OracleSpec ENNReal BigOperators

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β γ : Type}

section list

variable (oa : OracleComp spec α) (ob : OracleComp spec (List α))
  (x : α) (xs : List α)

@[simp]
lemma probOutput_seq_map_cons_eq_mul :
    [= x :: xs | (· :: ·) <$> oa <*> ob] = [= x | oa] * [= xs | ob] :=
  probOutput_seq_map_eq_mul_of_injective2 oa ob List.cons List.injective2_cons x xs

@[simp]
lemma probOutput_seq_map_cons_eq_mul' :
    [= x :: xs | (λ xs x ↦ x :: xs) <$> ob <*> oa] = [= x | oa] * [= xs | ob] :=
  (probOutput_seq_map_swap (· :: ·) oa ob (x :: xs)).trans
    (probOutput_seq_map_cons_eq_mul oa ob x xs)

end list

section vector

variable {n : ℕ} (oa : OracleComp spec α) (ob : OracleComp spec (Vector α n))
  (x : α) (xs : Vector α n)

@[simp]
lemma probOutput_seq_map_vector_cons_eq_mul :
    [= x ::ᵥ xs | (· ::ᵥ ·) <$> oa <*> ob] = [= x | oa] * [= xs | ob] :=
  probOutput_seq_map_eq_mul_of_injective2 oa ob Vector.cons Vector.injective2_cons x xs

@[simp]
lemma probOutput_seq_map_vector_cons_eq_mul' :
    [= x ::ᵥ xs | (λ xs x ↦ x ::ᵥ xs) <$> ob <*> oa] = [= x | oa] * [= xs | ob] :=
  (probOutput_seq_map_swap (· ::ᵥ ·) oa ob (x ::ᵥ xs)).trans
    (probOutput_seq_map_vector_cons_eq_mul oa ob x xs)

end vector
