/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
/-!
# Spec theorem for `ProjectiveNielsPoint::neg`

This function computes the negation of a ProjectiveNielsPoint. Given a point
N = (Y+X, Y−X, Z, 2dXY), it returns −N by swapping Y_plus_X and Y_minus_X,
keeping Z unchanged, and negating T2d.

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs, lines 503:4-510:5"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint
open curve25519_dalek.backend.serial.curve_models

namespace curve25519_dalek.Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint

/-- **Spec theorem for
`Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint.neg`**

Returns the negation of a ProjectiveNielsPoint:
- No panic (always returns successfully)
- Given input `self` with coordinates (Y_plus_X, Y_minus_X, Z, T2d), the output
ProjectiveNielsPoint has coordinates (Y_plus_X', Y_minus_X', Z', T2d') where::
  - Y_plus_X' = Y_minus_X (coordinates are swapped)
  - Y_minus_X' = Y_plus_X (coordinates are swapped)
  - Z' = Z (Z coordinate is unchanged)
  - T2d' ≡ -T2d (mod p) (T2d is negated modulo p = 2^255 - 19) -/
@[step]
theorem neg_spec
    (self : ProjectiveNielsPoint) (self_bound : ∀ i < 5, self.T2d[i]!.val < 2 ^ 54) :
    neg self ⦃ (result : ProjectiveNielsPoint) =>
      result.Y_plus_X = self.Y_minus_X ∧
      result.Y_minus_X = self.Y_plus_X ∧
      result.Z = self.Z ∧
      (Field51_as_Nat self.T2d + Field51_as_Nat result.T2d) % p = 0 ⦄ := by
  unfold neg
  step*
  simp_all [Nat.ModEq]

end curve25519_dalek.Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint
