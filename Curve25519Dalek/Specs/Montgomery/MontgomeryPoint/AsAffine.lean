/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Defs.Edwards.Representation

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

/-- Validity predicate for Montgomery projective points.
    A projective point (U : W) is valid if W is non-zero in the field. -/
def IsValid (pp : montgomery.ProjectivePoint) : Prop :=
  pp.W.toField ≠ 0

/-- Convert a valid projective point to its affine u-coordinate in the field. -/
noncomputable def toAffineField (pp : montgomery.ProjectivePoint)
    (_h : IsValid pp) : ZMod p :=
  pp.U.toField / pp.W.toField

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

@[progress]
theorem as_affine_spec (self : montgomery.ProjectivePoint)
    (h_valid : IsValid self) :
    ∃ res,
    as_affine self = ok res ∧
    MontgomeryPoint.IsValid res ∧
    bytesToField res = self.U.toField  / self.W.toField := by
  sorry

-- /-- Weaker spec: as_affine succeeds when W is non-zero -/
-- theorem as_affine_succeeds (self : montgomery.ProjectivePoint)
--     (h_W_nonzero : self.W.toField ≠ 0) :
--     ∃ res, as_affine self = ok res := by
--   sorry

end curve25519_dalek.montgomery.ProjectivePoint
