/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes

/-! # Spec Theorem for `ProjectivePoint::as_affine`

Specification and proof for
`curve25519_dalek::montgomery::{curve25519_dalek::montgomery::ProjectivePoint}::as_affine`.

This function converts a Montgomery projective point (U : W) to its affine representation
by computing u = U/W and encoding it as a 32-byte MontgomeryPoint.

**Source**: curve25519-dalek/src/montgomery.rs, lines 330:4-333:5

## TODO
- Complete proof
--/

open Aeneas.Std Result
open Montgomery
namespace curve25519_dalek.montgomery.ProjectivePoint

/-
Natural language description:

    • Converts a projective point (U : W) in Montgomery form to affine coordinates

    • Computes the affine u-coordinate as U/W via:
      - Inverts the W coordinate using field inversion
      - Multiplies U by W⁻¹ to obtain u = U/W
      - Converts the resulting field element to a 32-byte encoding

    • The projective coordinates (U : W) and (λU : λW) represent the same affine point
      for any non-zero λ in the field

Natural language specs:

    • The function succeeds when W is invertible (W ≠ 0 in the field)
    • Returns a 32-byte MontgomeryPoint encoding the affine u-coordinate
    • The result represents the u-coordinate on the Montgomery curve y² = x³ + Ax² + x
    • The conversion is deterministic and well-defined for valid projective points
-/

-- lemma bytesToField_eq_cast (a : Aeneas.Std.Array U8 32#usize) :
--     bytesToField a = (U8x32_as_Nat a : ZMod p) := by
--   sorry


/-- **Spec and proof concerning `montgomery.ProjectivePoint.as_affine`**:
- The function succeeds if and only if the W coordinate is non-zero in the field
- When successful, returns a MontgomeryPoint encoding the affine u-coordinate
- Mathematical properties of the result:
  * If the projective point is (U : W) with W ≠ 0, the result encodes u = U/W (mod p)
  * The encoded value satisfies: bytesToField(result) ≡ U/W (mod p)
  * Projective equivalence: (U : W) and (λU : λW) produce the same affine encoding
    for any non-zero λ in the field
  * The result is a valid MontgomeryPoint (32-byte array with value reduced modulo 2^255-19)
  * The computation uses constant-time field arithmetic operations
-/


lemma Field51_modP_ne_zero_of_toField_ne_zero
    (W : backend.serial.u64.field.FieldElement51)
    (hW : W.toField ≠ 0) :
    Field51_as_Nat W % p ≠ 0 := by
  intro hmod
  apply hW
  unfold curve25519_dalek.backend.serial.u64.field.FieldElement51.toField
  exact Edwards.lift_mod_eq (Field51_as_Nat W) 0 (by
    simpa [Nat.zero_mod] using hmod)

/-- Division in ZMod p equals multiplication by inverse when we have modular multiplicative inverse. -/
lemma zmod_div_eq_mul_of_mod_inv (U W x_inv : Nat) (hW_ne : W % p ≠ 0) (h_inv : x_inv * W ≡ 1 [MOD p]) :
    (U : ZMod p) / (W : ZMod p) = (U : ZMod p) * (x_inv : ZMod p) := by
  have h_mul : (x_inv : ZMod p) * (W : ZMod p) = 1 := by
    rw [Nat.ModEq] at h_inv
    calc (x_inv : ZMod p) * (W : ZMod p)
        = (((x_inv * W) : Nat) : ZMod p) := by norm_cast
      _ = (((x_inv * W) % p : Nat) : ZMod p) := by rw [ZMod.natCast_mod]
      _ = ((1 % p : Nat) : ZMod p) := by rw [h_inv]
      _ = (1 : ZMod p) := by norm_num
  have hW_ne_zero : (W : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at h
    exact hW_ne h
  rw [div_eq_mul_inv]
  congr 1
  symm
  exact (mul_eq_one_iff_eq_inv₀ hW_ne_zero).mp h_mul

@[progress]
theorem as_affine_spec (self : montgomery.ProjectivePoint)
    (hU : ∀ i < 5, self.U[i]!.val < 2 ^ 54)
    (hW : ∀ i < 5, self.W[i]!.val < 2 ^ 54)
    (h_valid : self.W.toField ≠ 0 ∧ self.U.toField / self.W.toField ≠ -1) :
    ∃ res,
    as_affine self = ok res ∧
    MontgomeryPoint.IsValid res ∧
    U8x32_as_Nat res = self.U.toField  / self.W.toField := by
  unfold as_affine at *
  progress*
  · -- Show MontgomeryPoint.IsValid res
    grind
  · -- Show bytesToField res = self.U.toField / self.W.toField
    constructor
    · unfold MontgomeryPoint.IsValid
      intro u
      by_cases h1 : u + 1 = 0
      · simp only [h1]
        have hu : u = -1 := by linear_combination h1
        have a_eq_div : U8x32_as_Nat a = self.U.toField / self.W.toField := by
          have h_W_nat_nonzero : Field51_as_Nat self.W % p ≠ 0 := Field51_modP_ne_zero_of_toField_ne_zero self.W h_valid.1
          rename_i x_inv _ x_inv_post u_inv _
          rcases h_valid with ⟨h_W_nonzero, h_U_div_W_ne_neg_one⟩
          have h_inv : Field51_as_Nat x_inv % p * (Field51_as_Nat self.W % p) % p = 1 := by
            exact x_inv_post h_W_nat_nonzero
          have h_inv2 : Field51_as_Nat x_inv * Field51_as_Nat self.W ≡ 1 [MOD p] := by
            dsimp [Nat.ModEq]
            calc
              (Field51_as_Nat x_inv * Field51_as_Nat self.W) % p
                  = (Field51_as_Nat x_inv % p *
                    (Field51_as_Nat self.W % p)) % p := by
                      simp [Nat.mul_mod]
              _ = 1 := by simp [h_inv]
          have h_inv4: self.U.toField / self.W.toField = (Field51_as_Nat self.U) / (Field51_as_Nat self.W) := by
            unfold curve25519_dalek.backend.serial.u64.field.FieldElement51.toField
            simp
          have h_inv5: (Field51_as_Nat self.U:ZMod p) / (Field51_as_Nat self.W:ZMod p) = Field51_as_Nat self.U * Field51_as_Nat x_inv := by
            exact zmod_div_eq_mul_of_mod_inv (Field51_as_Nat self.U) (Field51_as_Nat self.W) (Field51_as_Nat x_inv) h_W_nat_nonzero h_inv2
          rw [h_inv4, h_inv5]
          have h_chain2 := Nat.ModEq.trans a_post_1 u_post_1
          have h_eq_zmod2 := Edwards.lift_mod_eq (U8x32_as_Nat a) (Field51_as_Nat self.U * Field51_as_Nat x_inv) h_chain2
          have h_eq_zmod3 : (U8x32_as_Nat a : ZMod p) = (Field51_as_Nat self.U : ZMod p) * (Field51_as_Nat x_inv : ZMod p) := by
            rw [h_eq_zmod2, Nat.cast_mul]
          exact h_eq_zmod3
        have div_eq_neg_one : self.U.toField / self.W.toField = -1 := by
          -- This proof requires bytesToField_eq_cast lemma (line 51-53)
          -- which states: bytesToField a = (U8x32_as_Nat a : ZMod p)
          -- Once that lemma is proven, this calc chain will work:
          sorry
          -- calc self.U.toField / self.W.toField
          --     = ↑(U8x32_as_Nat a) := a_eq_div.symm
          --   _ = bytesToField a := (bytesToField_eq_cast a).symm
          --   _ = u := rfl
          --   _ = -1 := hu
        exact absurd div_eq_neg_one h_valid.2
      · sorry -- TODO: Do not complete the proof for since IsValid is still being modified
    · rename_i x_inv _ x_inv_post _
      have h_W_nat_nonzero : Field51_as_Nat self.W % p ≠ 0 := Field51_modP_ne_zero_of_toField_ne_zero self.W h_valid.1
      have h_inv : Field51_as_Nat x_inv % p * (Field51_as_Nat self.W % p) % p = 1 := by
        exact x_inv_post h_W_nat_nonzero
      have h_inv2 : Field51_as_Nat x_inv * Field51_as_Nat self.W ≡ 1 [MOD p] := by
        dsimp [Nat.ModEq]
        calc
          (Field51_as_Nat x_inv * Field51_as_Nat self.W) % p
              = (Field51_as_Nat x_inv % p *
                (Field51_as_Nat self.W % p)) % p := by
                  simp [Nat.mul_mod]
          _ = 1 := by simp [h_inv]
      have h_inv4: self.U.toField / self.W.toField = (Field51_as_Nat self.U) / (Field51_as_Nat self.W) := by
        unfold curve25519_dalek.backend.serial.u64.field.FieldElement51.toField
        simp
      have h_inv5: (Field51_as_Nat self.U:ZMod p) / (Field51_as_Nat self.W:ZMod p) = Field51_as_Nat self.U * Field51_as_Nat x_inv := by
        exact zmod_div_eq_mul_of_mod_inv (Field51_as_Nat self.U) (Field51_as_Nat self.W) (Field51_as_Nat x_inv) h_W_nat_nonzero h_inv2
      rw [h_inv4, h_inv5]
      have h_chain2 := Nat.ModEq.trans a_post_1 u_post_1
      have h_eq_zmod2 := Edwards.lift_mod_eq (U8x32_as_Nat a) (Field51_as_Nat self.U * Field51_as_Nat x_inv) h_chain2
      have h_eq_zmod3 : (U8x32_as_Nat a : ZMod p) = (Field51_as_Nat self.U : ZMod p) * (Field51_as_Nat x_inv : ZMod p) := by
        rw [h_eq_zmod2, Nat.cast_mul]
      exact h_eq_zmod3

end curve25519_dalek.montgomery.ProjectivePoint
