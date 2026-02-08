/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Defs.Edwards.Representation
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
open curve25519_dalek.backend.serial.u64
open curve25519_dalek
open curve25519_dalek.backend.serial.curve_models.curve25519_dalek.montgomery

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

-- /-- Validity predicate for Montgomery projective points.
--     A projective point (U : W) is valid if W is non-zero in the field. -/
def IsValid (pp : montgomery.ProjectivePoint) : Prop :=
  pp.W.toField ≠ 0 ∧ pp.U.toField / pp.W.toField ≠ -1

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

-- Helper lemma: bytesToField equals U8x32_as_Nat cast to ZMod p
lemma invert_mul_eq_div
  (U W x : backend.serial.u64.field.FieldElement51)
  (hx : Field51_as_Nat x * Field51_as_Nat W ≡ 1 [MOD p]) :
  Field51_as_Nat U * Field51_as_Nat x ≡ Field51_as_Nat U / Field51_as_Nat W [MOD p]
:= by
sorry

/-- If a limb-representation is nonzero in `ZMod p`, its canonical representative mod `p` is nonzero. -/
lemma Field51_modP_ne_zero_of_toField_ne_zero
    (W : backend.serial.u64.field.FieldElement51)
    (hW : W.toField ≠ 0) :
    Field51_as_Nat W % p ≠ 0 := by
  intro hmod
  apply hW
  unfold curve25519_dalek.backend.serial.u64.field.FieldElement51.toField
  exact Edwards.lift_mod_eq (Field51_as_Nat W) 0 (by
    simpa [Nat.zero_mod] using hmod)

@[progress]
theorem as_affine_spec (self : montgomery.ProjectivePoint)
    (hU : ∀ i < 5, self.U[i]!.val < 2 ^ 54)
    (hW : ∀ i < 5, self.W[i]!.val < 2 ^ 54)
    (h_valid : IsValid self) :
    ∃ res,
    as_affine self = ok res ∧
    MontgomeryPoint.IsValid res ∧
    bytesToField res = self.U.toField  / self.W.toField := by
  unfold as_affine IsValid at *
  -- Apply progress to handle the monad operations and get postconditions
  progress*
  -- Now build the final result
  -- constructor
  · -- Show MontgomeryPoint.IsValid res
    grind
  · -- Show bytesToField res = self.U.toField / self.W.toField
    constructor
    · unfold MontgomeryPoint.IsValid
      intro u
      by_cases h1 : u + 1 = 0
      · simp [h1]
        -- u + 1 = 0 means u = -1 in ZMod p
        have hu : u = -1 := by linear_combination h1
        -- Now show bytesToField a = self.U.toField / self.W.toField using invert_mul_eq_div
        have a_eq_div : bytesToField a = self.U.toField / self.W.toField := by
          have h_W_nat_nonzero : Field51_as_Nat self.W % p ≠ 0 := Field51_modP_ne_zero_of_toField_ne_zero self.W h_valid.1
          rename_i x_inv _ x_inv_post _ _
          rcases h_valid with ⟨h_W_nonzero, h_U_div_W_ne_neg_one⟩
          have h_inv : Field51_as_Nat x_inv % p * (Field51_as_Nat self.W % p) % p = 1 := by
            exact x_inv_post h_W_nat_nonzero
          sorry
        -- From a_eq_div and hu, we get self.U.toField / self.W.toField = -1
        -- This contradicts h_valid.2
        have div_eq_neg_one : self.U.toField / self.W.toField = -1 := by
          calc self.U.toField / self.W.toField
              = bytesToField a := a_eq_div.symm
            _ = u := rfl
            _ = -1 := hu
        exact absurd div_eq_neg_one h_valid.2
      · sorry
    · sorry

end curve25519_dalek.montgomery.ProjectivePoint
