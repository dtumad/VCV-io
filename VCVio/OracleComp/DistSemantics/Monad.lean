/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist

/-!
# Probability Lemmas About Monad Operations

This file contains lemmas about `evalDist` applied to monadic operations like `pure` and `bind`.
-/


open OracleSpec OracleComp Option ENNReal Function

section scratch

universe u v w
