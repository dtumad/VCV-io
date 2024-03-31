/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp

/-!
# Hard Homogeneous Spaces

This file builds up the definition of a hard homogeneous space, an extension of a group action
on some set such that the action of each group element defines a bijection.
We use mathlib's `AddTorsor` type class to represent the bijection property,
and extend this with finiteness and decidability conditions
-/

/-- A `HomogeneousSpace G P` is a group action of a group `G` on a set of points `P`,
such that the action induces a bijection (represented by the `AddTorsor` class),
with the additional assumption that both spaces are finite. -/
class HomogeneousSpace (G : outParam Type) (P : semiOutParam Type)
    [outParam (AddGroup G)]
    extends AddTorsor G P where
  fintype_G : Fintype G
  fintype_P : Fintype P
  -- `AddTorsor G P` only gives us a `Nonemtpy` instance
  -- inhabited_P : Inhabited P
  decidableEq_G : DecidableEq G
  decidableEq_P : DecidableEq P

namespace HomogeneousSpace

variable {G P : Type} [AddGroup G]

-- #check AddGroup.inhabited

instance [h : HomogeneousSpace G P] : Fintype G := h.fintype_G
instance [h : HomogeneousSpace G P] : Fintype P := h.fintype_P

-- instance : Inhabited G := ⟨0⟩
instance [h : HomogeneousSpace G P] : DecidableEq G := h.decidableEq_G
instance [h : HomogeneousSpace G P] : DecidableEq P := h.decidableEq_P

/-- An adversary for the vectorization game takes in a pair of base points `(x₁, x₂)`,
and attempts to generate a vectorization, i.g. a vector `g` with `g +ᵥ x₂ = x₁`.

TODO: how does ":=" compare to "extends" in practice? -/
structure vectorizationAdv (G P : Type)
  extends SecAdv unifSpec (P × P) G

-- /-- Analogue of the game for the discrete logarithm assumption.
-- The input generator randomly chooses the challenge points for the adversary,
-- and a result is valid if it is exactly the vectorization of the challenge points. -/
-- noncomputable def vectorizationExp [HomogeneousSpace G P]
--     (adv : vectorizationAdv G P) : SecExp unifSpec (P × P) G where
--   inpGen := do let x₁ ← $ᵗ P; let x₂ ← $ᵗ P; return (x₁, x₂)
--   main := adv.run
--   isValid := λ ⟨x₁, x₂⟩ g ↦ g = x₁ -ᵥ x₂
--   __ := OracleAlg.baseOracleAlg

namespace vectorizationExp



end vectorizationExp

end HomogeneousSpace
