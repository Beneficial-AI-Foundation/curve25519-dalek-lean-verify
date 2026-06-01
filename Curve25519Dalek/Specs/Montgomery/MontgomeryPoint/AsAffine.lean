/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes

/-!
# Spec theorem for `curve25519_dalek::montgomery::ProjectivePoint::as_affine`

Converts a projective point `(U : W)` to its affine u-coordinate by computing `U / W` and
encoding the result as a 32-byte `MontgomeryPoint`:

• Inverts `W`, multiplies `U` by `W⁻¹`, and encodes the result as 32 bytes
• Projective equivalence: `(U : W)` and `(λU : λW)` produce identical output
• Pure encoding function; does not verify that the result lies on the curve

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery
namespace curve25519_dalek.montgomery.ProjectivePoint

/-- If `W.toField ≠ 0`, then `Field51_as_Nat W % p ≠ 0`. -/
lemma Field51_modP_ne_zero_of_toField_ne_zero
    (W : backend.serial.u64.field.FieldElement51)
    (hW : W.toField ≠ 0) :
    Field51_as_Nat W % p ≠ 0 := by
  intro hmod
  apply hW
  unfold backend.serial.u64.field.FieldElement51.toField
  exact Edwards.lift_mod_eq (Field51_as_Nat W) 0 (by
    simpa [Nat.zero_mod] using hmod)

/-- Division in ZMod p equals multiplication by inverse when we have modular
multiplicative inverse. -/
lemma zmod_div_eq_mul_of_mod_inv (U W x_inv : Nat) (hW_ne : W % p ≠ 0)
    (h_inv : x_inv * W ≡ 1 [MOD p]) :
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

/-- **Spec theorem for `curve25519_dalek::montgomery::ProjectivePoint::as_affine`**
• No panic (always returns successfully when input limbs satisfy bounds)
• Returns `bytesToField(result) = U / W (mod p)` where `p = 2^255 - 19`
• The natural-number value of the result satisfies `U8x32_as_Nat result < 2^255`
-/
@[step]
theorem as_affine_spec (self : ProjectivePoint)
    (hU : self.U.IsValid)
    (hW : self.W.IsValid)
    (h_valid : self.W.toField ≠ 0) :
    as_affine self ⦃ (result : MontgomeryPoint) =>
      U8x32_as_Field result = self.U.toField / self.W.toField ∧
      U8x32_as_Nat result < 2^255 ⦄ := by
  unfold as_affine at *
  step*
  · constructor
    · rename_i fe_inv h_mul_U_Winv
      have h_W_nat_nonzero : Field51_as_Nat self.W % p ≠ 0 :=
        Field51_modP_ne_zero_of_toField_ne_zero self.W h_valid
      have h_inv : Field51_as_Nat fe % p * (Field51_as_Nat self.W % p) % p = 1 := by
        exact fe_post1 h_W_nat_nonzero
      have h_inv2 : Field51_as_Nat fe * Field51_as_Nat self.W ≡ 1 [MOD p] := by
        dsimp [Nat.ModEq]
        calc
          (Field51_as_Nat fe * Field51_as_Nat self.W) % p
              = (Field51_as_Nat fe % p *
                (Field51_as_Nat self.W % p)) % p := by
                  simp [Nat.mul_mod]
          _ = 1 := by simp [h_inv]
      have h_inv4 : self.U.toField / self.W.toField =
          (Field51_as_Nat self.U) / (Field51_as_Nat self.W) := by
        unfold backend.serial.u64.field.FieldElement51.toField
        simp
      have h_inv5 : (Field51_as_Nat self.U : ZMod p) / (Field51_as_Nat self.W : ZMod p) =
          Field51_as_Nat self.U * Field51_as_Nat fe := by
        exact zmod_div_eq_mul_of_mod_inv (Field51_as_Nat self.U)
          (Field51_as_Nat self.W) (Field51_as_Nat fe) h_W_nat_nonzero h_inv2
      rw [h_inv4, h_inv5]
      have h_chain2 := Nat.ModEq.trans a_post1 u_post1
      have h_eq_zmod2 := Edwards.lift_mod_eq (U8x32_as_Nat a)
        (Field51_as_Nat self.U * Field51_as_Nat fe) h_chain2
      have h_eq_zmod3 : (U8x32_as_Nat a : ZMod p) =
          (Field51_as_Nat self.U : ZMod p) * (Field51_as_Nat fe : ZMod p) := by
        rw [h_eq_zmod2, Nat.cast_mul]
      grind only [U8x32_as_Field_eq_cast]
    · apply lt_trans a_post2
      decide

end curve25519_dalek.montgomery.ProjectivePoint
