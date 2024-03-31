/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.HardHomogeneousSpace

/-!
# Diffie Hellman Assumptions

This file gives a way to represent assumptions such as discrete log or Diffie Hellman.
We represent this as hardness assumptions on the corresponding hard homogenous space.
-/

namespace DiffieHellman

-- @[inline, reducible]
def DHPoint (p : ℕ) : Type := ZMod p

-- @[inline, reducible]
def DHVec (p : ℕ) : Type := ZMod p

def DHPoint.to_zmod (x : DHPoint p) : ZMod p := x
def DHVec.to_zmod (x : DHVec p) : ZMod p := x

instance (p : ℕ) : Coe (DHPoint p) (ZMod p) := ⟨id⟩
instance (p : ℕ) : Coe (DHVec p) (ZMod p) := ⟨id⟩

-- example (p : ℕ) [Fact (Nat.Prime (p))] : Group (ZMod (p)) := by
--   have := ZMod.instFieldZMod (p)

instance (p : ℕ) : Add (DHVec p) := ⟨λ x y ↦ x.to_zmod * y.to_zmod⟩
instance (p : ℕ) : Zero (DHVec p) := ⟨(1 : ZMod p)⟩
instance (p : ℕ) [Fact (Nat.Prime p)] : Neg (DHVec p) := ⟨λ x ↦ (x.to_zmod⁻¹ : ZMod p)⟩
instance (p : ℕ) [Fact (Nat.Prime p)] : Sub (DHVec p) := ⟨λ x y ↦ x.to_zmod / y.to_zmod⟩

instance (p : ℕ) [Fact (Nat.Prime p)] : AddGroup (DHVec p) where
  add_assoc := λ x y z ↦ mul_assoc x.to_zmod y.to_zmod z.to_zmod
  zero_add := λ x ↦ one_mul x.to_zmod
  add_zero := λ x ↦ mul_one x.to_zmod
  nsmul := nsmulRec
  -- nsmul_zero := λ x ↦ rfl
  -- nsmul_succ := λ x n ↦ rfl
  -- sub_eq_add_neg := λ _ _ ↦ rfl
  zsmul := zsmulRec
  -- zsmul_zero' := λ
  -- zsmul_succ' := _
  -- zsmul_neg' := _
  add_left_neg := λ x ↦ sorry

#check ZMod.nat_cast_val

-- def DHHomogenousSpace (p : outParam ℕ) [Fact (Nat.Prime p)] :
--     HomogeneousSpace (DHVec p) (DHPoint p) where
--   vadd := _
--   zero_vadd := _
--   add_vadd := _
--   vsub := _
--   vsub_vadd' := _
--   vadd_vsub' := _

--   nonempty := ⟨(0 : ZMod p)⟩
--   fintype_G := ZMod.fintype p
--   fintype_P := ZMod.fintype p
--   -- inhabited_G :=
--   -- inhabited_P := _
--   decidableEq_G := _
--   decidableEq_P := _

end DiffieHellman
