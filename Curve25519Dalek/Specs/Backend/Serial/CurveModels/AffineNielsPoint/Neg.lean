/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg

/-! # Spec theorem for `curve25519_dalek::backend::serial::curve_models::AffineNielsPoint::neg`

This function implements the negation of a point in affine Niels coordinates.
Given an AffineNielsPoint N = (y+x, y−x, 2dxy), it computes -N by:
- Swapping y_plus_x and y_minus_x
- Negating xy2d

The concrete formulas are:
- y_plus_x'  = y_minus_x
- y_minus_x' = y_plus_x
- xy2d'      = -xy2d

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.curve_models
namespace curve25519_dalek.Shared0AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint

/-- **Spec theorem for `curve25519_dalek::backend::serial::curve_models::AffineNielsPoint::neg`**
• The function always succeeds (no panic) for an AffineNielsPoint `self` with coordinates
(y_plus_x, y_minus_x, xy2d)
• The output AffineNielsPoint computed by `neg self` has coordinates (y_plus_x', y_minus_x', xy2d')
  • y_plus_x' = y_minus_x (the coordinates are swapped)
  • y_minus_x' = y_plus_x (the coordinates are swapped)
  • `xy2d' ≡ -xy2d (mod p)` (the xy2d coordinate is negated modulo p = 2^255 - 19) -/
@[step]
theorem neg_spec
    (self : backend.serial.curve_models.AffineNielsPoint)
    (self_bound : ∀ i < 5, self.xy2d[i]!.val < 2 ^ 54) :
    neg self ⦃ (result : AffineNielsPoint) =>
      result.y_plus_x = self.y_minus_x ∧
      result.y_minus_x = self.y_plus_x ∧
      (Field51_as_Nat self.xy2d + Field51_as_Nat result.xy2d) % p = 0 ⦄ := by
  unfold neg
  step*
  simp_all [Nat.ModEq]

end curve25519_dalek.Shared0AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint

namespace curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
namespace CoreOpsArithNegAffineNielsPoint

/-- **Spec theorem for `curve25519_dalek::backend::serial::curve_models::AffineNielsPoint::neg`**

Specification for the owned-value
`curve25519_dalek::backend::serial::curve_models::AffineNielsPoint::neg`.
• The function always succeeds (no panic) for an AffineNielsPoint `self` with coordinates
  (y_plus_x, y_minus_x, xy2d) satisfying the limb bound `self.xy2d[i] < 2^54`
• The output AffineNielsPoint computed by `neg self` has coordinates (y_plus_x', y_minus_x', xy2d')
  • y_plus_x' = y_minus_x (the coordinates are swapped)
  • y_minus_x' = y_plus_x (the coordinates are swapped)
  • `xy2d' ≡ -xy2d (mod p)` (the xy2d coordinate is negated modulo p = 2^255 - 19)

Mirrors the shared-reference `Shared0…neg_spec`; the owned `neg` is just a
one-step delegation to it (Rust source: `-&self`). -/
@[step]
theorem neg_spec
    (self : backend.serial.curve_models.AffineNielsPoint)
    (self_bound : ∀ i < 5, self.xy2d[i]!.val < 2 ^ 54) :
    neg self ⦃ (result : AffineNielsPoint) =>
      result.y_plus_x = self.y_minus_x ∧
      result.y_minus_x = self.y_plus_x ∧
      (Field51_as_Nat self.xy2d + Field51_as_Nat result.xy2d) % p = 0 ⦄ := by
  unfold neg
  exact Shared0AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint.neg_spec
    self self_bound

end CoreOpsArithNegAffineNielsPoint
end curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
