import Mathlib.Data.PFunctor.Multivariate.Basic
import VCVio.OracleComp.OracleSpec

/-!
  # Polynomial Functors

  We want to define a bunch of missing definitions for polynomial functors, with a view towards
  defining the free monad on a polynomial functor (which does not raise the universe level), and
  also to model interactive protocols.
-/

universe u v

-- Oracle queries can be seen as a special case of polynomial functors
-- i.e. `A` is the sigma type `(i : ι) × (spec.domain i)` and
-- `B` is the function `fun ⟨i, _⟩ => spec.range i`

variable {ι : Type u} (spec : OracleSpec ι)

def OracleSpec.toPFunctor : PFunctor :=
  PFunctor.mk (Σ i : ι, spec.domain i) (fun ⟨i, _⟩ => spec.range i)

alias PFunctor.ofOracleSpec := OracleSpec.toPFunctor

def OracleQuery := PFunctor.W spec.toPFunctor

inductive PFunctor.FreeMonad (P : PFunctor.{u}) : Type v → Type (max u v)
  | pure {α} (x : α) : FreeMonad P α
  | roll {α} (a : P.A) (f : P.B a → FreeMonad P α) : FreeMonad P α
