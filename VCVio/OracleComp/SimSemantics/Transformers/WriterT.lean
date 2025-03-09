/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.Prod
import ToMathlib.Control.WriterT

/-!
# Simulation using `WriterT` Monad Transformers

Lemmas about `simulateQ` with output monad `WriterT ω (OracleComp spec)` for some `ω`
-/

open OracleSpec OracleComp Function Prod

universe u v w
@[simp]
lemma fst_map_writerT_run_simulateQ {ι : Type u} {spec : OracleSpec ι} {α : Type u}
    {ω : Type u} [Monoid ω] {so : QueryImpl spec (WriterT ω (OracleComp spec))}
    (hso : ∀ {α}, ∀ q : OracleQuery spec α, fst <$> (so.impl q).run = q)
    (oa : OracleComp spec α) : fst <$> (simulateQ so oa).run = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa h =>
      simp_rw [simulateQ_bind, simulateQ_query, WriterT.run_bind, map_bind, Functor.map_map,
        map_fst, id_eq, h, ← (congr_arg (· >>= oa) (hso (query i t))), bind_map_left]
  | failure => simp

@[simp]
lemma probFailure_writerT_run_simulateQ {ι : Type u} {spec : OracleSpec ι} [spec.FiniteRange] {α : Type u}
    {ω : Type u} [Monoid ω] {so : QueryImpl spec (WriterT ω (OracleComp spec))}
    (hso : ∀ {α}, ∀ q : OracleQuery spec α, fst <$> (so.impl q).run = q)
    (hso' : ∀ {α}, ∀ q : OracleQuery spec α, [⊥ | (so.impl q).run] = 0)
    (oa : OracleComp spec α) : [⊥ | (simulateQ so oa).run] = [⊥ | oa] := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa h =>
      simp [probFailure_bind_eq_tsum, h, hso']
      rw [ENNReal.tsum_prod']
      refine tsum_congr fun x => ?_
      simp [ENNReal.tsum_mul_right]
      congr 1
      calc ∑' (w : ω), [=(x, w) | (so.impl (query i t)).run]
        _ = [= x | fst <$> (so.impl (query i t)).run] := by rw [probOutput_fst_map_eq_tsum]
        _ = (↑(Fintype.card (spec.range i)))⁻¹ := by rw [hso, probOutput_query]
  | failure => simp
