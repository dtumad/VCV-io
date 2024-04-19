/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleComp
import Mathlib.Data.Set.Finite

/-!
# Oracles Used by a Computation

This file defines a function `OracleComp.activeOracles : OracleComp spec α → Set α` that
gives the set of possible outputs of a computation, assuming all oracle outputs are possible.

If the final output type has decidable equality we can also define a function
`OracleComp.finSupport : OracleComp spec α → Finset α` with the same property.
This relies on decidable equality instances in `OracleSpec` as well, and the definition
would need to be adjusted if those were moved into a seperate typeclass.

We avoid using `(evalDist oa).support` as the definition of the support, as this forces
noncomputability due to the use of real numbers, and also makes defining `finSupport` harder.
-/

namespace OracleComp

variable {spec : OracleSpec} {α : Type}

def activeOracles : (oa : OracleComp spec α) → Finset spec.ι
  | pure' _ _ => ∅
  | queryBind' i _ _ oa => insert i
      (Finset.univ.biUnion (λ j ↦ activeOracles (oa j)))

end OracleComp
