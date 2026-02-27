/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
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

This function computes the affine u-coordinate u = U/W from a projective point (U : W)
and encodes it as a 32-byte MontgomeryPoint.

**Important**: This function does NOT verify that the result is a valid point on the
Montgomery curve. It mechanically computes U/W and encodes it as bytes. If the input
projective point does not represent a point on the curve, the output will not be a
valid curve point. Validity checking is the caller's responsibility.

**Source**: curve25519-dalek/src/montgomery.rs, lines 330:4-333:5

--/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery

namespace curve25519_dalek.montgomery.ProjectivePoint


/-
Natural language description:

    • Computes the affine u-coordinate from a projective point (U : W)

    • Computation steps:
      - Inverts the W coordinate using field inversion
      - Multiplies U by W⁻¹ to obtain u = U/W
      - Converts the resulting field element to a 32-byte encoding

    • Projective equivalence: (U : W) and (λU : λW) produce the same u-coordinate
      for any non-zero λ in the field

Natural language specs:

    • Precondition: Input field element limbs must satisfy bounds (< 2^54)
    • Precondition: W ≠ 0 (in the field)
    • Postcondition: The output correctly encodes u = U/W as a 32-byte array
    • Postcondition: bytesToField(result) = U/W (mod p)

    • No validity check: This function does NOT verify that u represents a point on
      the Montgomery curve. It is a pure encoding function.
    • Caller responsibility: If curve point validity is required, the caller must
      ensure the input projective point represents a valid curve point.
-/

lemma bytesToField_eq_cast (a : Aeneas.Std.Array U8 32#usize) :
    bytesToField a = (U8x32_as_Nat a : ZMod p) := by
  sorry

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

/-- **Specification for `montgomery.ProjectivePoint.as_affine`**:

This function computes the affine u-coordinate from projective coordinates (U : W)
and encodes it as a 32-byte MontgomeryPoint.

**Preconditions**:
- Input limbs satisfy bounds: U[i] < 2^54 and W[i] < 2^54 for all i < 5
- W ≠ 0 (mod p), ensuring the division U/W is well-defined

**Postcondition**:
- The output encodes u = U/W: bytesToField(result) = U/W (mod p)

**No validity guarantee**: This function does NOT check whether u represents a point
on the Montgomery curve y² = u³ + Au² + u. The output is simply the byte encoding of
the field element U/W, which may or may not correspond to a valid curve point.

**Note on Rust implementation**: The Rust type `MontgomeryPoint = [u8; 32]` is just
a byte array without invariants. Rust's type system does not encode "valid curve point"
as a constraint, so this function follows that design by not enforcing validity.

where p = 2^255 - 19
-/

@[progress]
theorem as_affine_spec (self : montgomery.ProjectivePoint)
    (hU : ∀ i < 5, self.U[i]!.val < 2 ^ 54)
    (hW : ∀ i < 5, self.W[i]!.val < 2 ^ 54)
    (h_valid : self.W.toField ≠ 0) :
    as_affine self ⦃ res => bytesToField res = self.U.toField  / self.W.toField  ⦄ := by
  unfold as_affine at *
  progress*
  · grind
  · rename_i fe_inv h_mul_U_Winv
    have h_W_nat_nonzero : Field51_as_Nat self.W % p ≠ 0 := Field51_modP_ne_zero_of_toField_ne_zero self.W h_valid
    have h_inv : Field51_as_Nat fe % p * (Field51_as_Nat self.W % p) % p = 1 := by
      exact fe_post_1 h_W_nat_nonzero
    have h_inv2 : Field51_as_Nat fe * Field51_as_Nat self.W ≡ 1 [MOD p] := by
      dsimp [Nat.ModEq]
      calc
        (Field51_as_Nat fe * Field51_as_Nat self.W) % p
            = (Field51_as_Nat fe % p *
              (Field51_as_Nat self.W % p)) % p := by
                simp [Nat.mul_mod]
        _ = 1 := by simp [h_inv]
    have h_inv4: self.U.toField / self.W.toField = (Field51_as_Nat self.U) / (Field51_as_Nat self.W) := by
      unfold curve25519_dalek.backend.serial.u64.field.FieldElement51.toField
      simp
    have h_inv5: (Field51_as_Nat self.U:ZMod p) / (Field51_as_Nat self.W:ZMod p) = Field51_as_Nat self.U * Field51_as_Nat fe := by
      exact zmod_div_eq_mul_of_mod_inv (Field51_as_Nat self.U) (Field51_as_Nat self.W) (Field51_as_Nat fe) h_W_nat_nonzero h_inv2
    rw [h_inv4, h_inv5]
    have h_chain2 := Nat.ModEq.trans a_post_1 u_post_1
    have h_eq_zmod2 := Edwards.lift_mod_eq (U8x32_as_Nat a) (Field51_as_Nat self.U * Field51_as_Nat fe) h_chain2
    have h_eq_zmod3 : (U8x32_as_Nat a : ZMod p) = (Field51_as_Nat self.U : ZMod p) * (Field51_as_Nat fe : ZMod p) := by
      rw [h_eq_zmod2, Nat.cast_mul]
    grind [bytesToField_eq_cast]

end curve25519_dalek.montgomery.ProjectivePoint
