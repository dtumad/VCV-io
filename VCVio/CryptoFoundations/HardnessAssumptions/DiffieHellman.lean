/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.HardnessAssumptions.HardHomogeneousSpace

/-!
# Diffie Hellman Assumptions

This file gives a way to represent assumptions such as discrete log or Diffie Hellman.
We represent this as hardness assumptions on the corresponding hard homogenous space.
-/

namespace DiffieHellman

def DHVec (p : ℕ) [Fact (Nat.Prime (p + 1))] : Type := { x : ZMod (p + 1) // x ≠ 0 }

@[inline, reducible]
def DHPoint (p : ℕ) [Fact (Nat.Prime (p + 1))] : Type := DHVec p

-- Having `NeZero p` is reduntant but simplifies things
variable (p : ℕ) [hp : Fact (Nat.Prime (p + 1))] [hp0 : NeZero p]

/-- "Fake" addition for the homogenous space, corresponding to multiplication in reality. -/
instance : Add (DHVec p) where
  add | ⟨x, hx⟩, ⟨y, hy⟩ => ⟨x * y, mul_ne_zero hx hy⟩

/-- The "zero" for this addition is the multiplicative identity. -/
instance : Zero (DHVec p) where
  zero := ⟨1, one_ne_zero⟩

/-- The "negation" for this addition is the multiplicative inverse. -/
instance : Neg (DHVec p) where
  neg | ⟨x, hx⟩ => ⟨x⁻¹, inv_ne_zero hx⟩

instance : AddGroup (DHVec p) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc | ⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩ => Subtype.ext (mul_assoc x y z)
  zero_add | ⟨x, hx⟩ => Subtype.ext (one_mul x)
  add_zero | ⟨x, hx⟩ => Subtype.ext (mul_one x)
  add_left_neg | ⟨x, hx⟩ => Subtype.ext (inv_mul_cancel hx)

/-- Homogenous space corresponding to discrete log problem in a finite field. -/
def DHHomogenousSpace : HomogeneousSpace (DHVec p) (DHPoint p) where
  vadd | ⟨x, hx⟩, ⟨y, hy⟩ => ⟨y ^ (x.1 : ℕ), by simp [hy]⟩
  vsub | ⟨x, hx⟩, ⟨y, hy⟩ => ⟨sorry, sorry⟩ -- Should be discrete log
  zero_vadd | ⟨x, hx⟩ => Subtype.ext (by show x ^ _ = x; simp [Nat.mod_eq, hp0.1])
  add_vadd | ⟨⟨x, _⟩, hx⟩, ⟨⟨y, _⟩, hy⟩, ⟨z, hz⟩ => Subtype.ext (by
    suffices z ^ (p + 1) = 1 by
      show z ^ _ = (z ^ _) ^ _
      simp only [Nat.add_eq, Nat.add_zero, ← pow_mul, mul_comm y x]
      exact (pow_eq_pow_mod (x * y) (this)).symm
    sorry
  )
  vsub_vadd' | ⟨x, hx⟩, ⟨y, hy⟩ => sorry
  vadd_vsub' | ⟨x, hx⟩, ⟨y, hy⟩ => sorry
  decidableEq_G := Subtype.instDecidableEqSubtype
  decidableEq_P := Subtype.instDecidableEqSubtype
  selectableType_G := sorry
  selectableType_P := sorry

end DiffieHellman
