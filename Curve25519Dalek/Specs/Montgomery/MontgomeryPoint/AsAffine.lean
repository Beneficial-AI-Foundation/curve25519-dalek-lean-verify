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

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery

-- in
namespace curve25519_dalek.montgomery.ProjectivePoint

-- set_option maxHeartbeats 400000

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

-- /-- **Spec and proof concerning `montgomery.ProjectivePoint.as_affine`**:
-- - No panic (always returns successfully) when input limbs satisfy bounds
-- - For the input projective point (U : W), the resulting MontgomeryPoint encodes:
--   * If W ≢ 0 (mod p): the affine u-coordinate where u ≡ U * W^(-1) (mod p)
--   * If W ≡ 0 (mod p): u ≡ 0 (mod p) (since invert returns 0 on input 0)
-- - The result is a valid 32-byte encoding with U8x32_as_Nat(result) < p
-- - Projective equivalence: (U : W) and (λU : λW) produce the same affine encoding
--   for any non-zero λ in the field (when W ≢ 0)
-- where p = 2^255 - 19
-- -/

-- @[progress]

theorem as_affine_spec (self : montgomery.ProjectivePoint)
    (hU : ∀ i < 5, self.U[i]!.val < 2 ^ 54)
    (hW : ∀ i < 5, self.W[i]!.val < 2 ^ 54)
    (h_valid : self.W.toField ≠ 0 ∧ self.U.toField / self.W.toField ≠ -1) :
    as_affine self ⦃ res =>
    MontgomeryPoint.IsValid res ∧
    bytesToField res = self.U.toField  / self.W.toField  ⦄ := by
  unfold as_affine at *
  progress*
  · grind
  -- · sorry
  · -- Show bytesToCurve25519Dalek/FunsExternal.leanField res = self.U.toField / self.W.toField
    constructor
    · unfold MontgomeryPoint.IsValid
      intro u
      by_cases h1 : u + 1 = 0
      · simp only [h1]
        have hu : u = -1 := by linear_combination h1
        have a_eq_div : U8x32_as_Nat a = self.U.toField / self.W.toField := by
          have h_W_nat_nonzero : Field51_as_Nat self.W % p ≠ 0 := Field51_modP_ne_zero_of_toField_ne_zero self.W h_valid.1
          rename_i hw_inv h_mul_U_Winv h_mul_bind
          --  _ x_inv_post u_inv
          rcases h_valid with ⟨h_W_nonzero, h_U_div_W_ne_neg_one⟩
          have h_inv : Field51_as_Nat fe % p * (Field51_as_Nat self.W % p) % p = 1 := by
            -- sorry
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
      · -- neg case: u + 1 ≠ 0
        simp only [h1, if_false]
        -- Need to establish that u corresponds to a valid Montgomery point
        have h_u_eq : u = self.U.toField / self.W.toField := by
          -- u is defined as bytesToField a, need to connect to U/W
          change bytesToField a = self.U.toField / self.W.toField
          rw [bytesToField_eq_cast]
          -- Similar proof to line 118-142, establishing a = U/W
          have h_W_nat_nonzero : Field51_as_Nat self.W % p ≠ 0 :=
            Field51_modP_ne_zero_of_toField_ne_zero self.W h_valid.1
          rename_i hw_inv h_mul_U_Winv h_mul_bind
          have h_inv : Field51_as_Nat fe % p * (Field51_as_Nat self.W % p) % p = 1 := by
            exact fe_post_1 h_W_nat_nonzero
          have h_inv2 : Field51_as_Nat fe * Field51_as_Nat self.W ≡ 1 [MOD p] := by
            dsimp [Nat.ModEq]
            calc (Field51_as_Nat fe * Field51_as_Nat self.W) % p
                = (Field51_as_Nat fe % p * (Field51_as_Nat self.W % p)) % p := by simp [Nat.mul_mod]
              _ = 1 := by simp [h_inv]
          have h_inv4: self.U.toField / self.W.toField =
              (Field51_as_Nat self.U) / (Field51_as_Nat self.W) := by
            unfold curve25519_dalek.backend.serial.u64.field.FieldElement51.toField
            simp
          have h_inv5: (Field51_as_Nat self.U:ZMod p) / (Field51_as_Nat self.W:ZMod p) =
              Field51_as_Nat self.U * Field51_as_Nat fe := by
            exact zmod_div_eq_mul_of_mod_inv (Field51_as_Nat self.U) (Field51_as_Nat self.W)
              (Field51_as_Nat fe) h_W_nat_nonzero h_inv2
          rw [h_inv4, h_inv5]
          have h_chain2 := Nat.ModEq.trans a_post_1 u_post_1
          have h_eq_zmod2 := Edwards.lift_mod_eq (U8x32_as_Nat a)
            (Field51_as_Nat self.U * Field51_as_Nat fe) h_chain2
          have h_eq_zmod3 : (U8x32_as_Nat a : ZMod p) =
              (Field51_as_Nat self.U : ZMod p) * (Field51_as_Nat fe : ZMod p) := by
            rw [h_eq_zmod2, Nat.cast_mul]
          exact h_eq_zmod3
        -- The goal is exactly the IsValid definition for Montgomery points!
        -- Since u = bytesToField a, we can rewrite the goal
        change IsSquare ((((bytesToField a - 1) * (bytesToField a + 1)⁻¹) ^ 2 - 1) *
          (↑d * ((bytesToField a - 1) * (bytesToField a + 1)⁻¹) ^ 2 + 1)⁻¹)
        -- Now this is exactly the IsValid condition for MontgomeryPoint a
        have h_valid_montgomery : MontgomeryPoint.IsValid a := by
          -- Need to prove: MontgomeryPoint.IsValid a
          -- We have:
          -- - h_valid.2 : self.U.toField / self.W.toField ≠ -1
          -- - h_u_eq : u = self.U.toField / self.W.toField
          -- - h1 : ¬u + 1 = 0 (which means bytesToField a + 1 ≠ 0)
          -- - a_post_2 : U8x32_as_Nat a < p
          --
          -- This requires proving that the computation preserves validity:
          -- If the input (U/W) is a valid Montgomery point (≠ -1),
          -- then the output bytes `a` also encode a valid Montgomery point.
          --
          -- This may require a new lemma connecting:
          -- 1. The mathematical u-coordinate (U/W)
          -- 2. The byte representation (a)
          -- 3. The IsValid property
          sorry
        unfold MontgomeryPoint.IsValid at h_valid_montgomery
        rw [if_neg] at h_valid_montgomery
        · exact h_valid_montgomery
        · exact h1
    ·
      rename_i fe_inv h_mul_U_Winv
      -- rename_i x_inv _ x_inv_post _
      have h_W_nat_nonzero : Field51_as_Nat self.W % p ≠ 0 := Field51_modP_ne_zero_of_toField_ne_zero self.W h_valid.1
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
      sorry
      -- exact h_eq_zmod3

end curve25519_dalek.montgomery.ProjectivePoint
