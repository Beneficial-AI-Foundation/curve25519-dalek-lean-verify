/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI Assistant
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg

/-! # Spec Theorem for `CompressedEdwardsY::decompress::step_2`

Specification and proof for the second step of `CompressedEdwardsY::decompress`.

This function performs the final decompression step which:
1. Extracts the sign bit from the compressed representation
2. Conditionally negates the x-coordinate according to the sign bit
3. Computes T = X * Y
4. Returns the complete EdwardsPoint in extended coordinates (X, Y, Z, T)

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51
namespace curve25519_dalek.edwards.CompressedEdwardsY

/-
Natural language description:

    - Takes a CompressedEdwardsY and field elements X, Y, Z from step_1
    - Extracts the sign bit from the high bit of byte 31 of the compressed representation
    - Since sqrt_ratio_i returns the nonnegative square root, conditionally negates X
      according to the sign bit to match the encoded sign
    - Computes T = X * Y (the product of x and y coordinates)
    - Returns an EdwardsPoint with coordinates (X, Y, Z, T)

Natural language specs:

    - The function always succeeds (no panic)
    - The sign bit is extracted from the high bit (bit 7) of byte 31
    - X is conditionally negated: if the sign bit is set, X becomes -X
    - T is computed as the product X * Y (mod p)
    - The returned point has Z unchanged from the input
    - The returned point satisfies T = X * Y (mod p)
-/

/-- **Spec for `edwards.decompress.step_2`**:
- No panic (always returns successfully)
- Returns an EdwardsPoint with coordinates (X', Y, Z, T) where:
  - The sign bit is extracted from bit 7 of byte 31 of the compressed representation
  - X' is conditionally negated based on the sign bit:
    - If sign bit is 0, X' = X
    - If sign bit is 1, X' = -X (mod p)
  - Y and Z are unchanged from the inputs
  - T = X' * Y (mod p)
-/
@[progress]
theorem step_2_spec
    (repr : edwards.CompressedEdwardsY)
    (X : backend.serial.u64.field.FieldElement51)
    (Y : backend.serial.u64.field.FieldElement51)
    (Z : backend.serial.u64.field.FieldElement51)
    (bytes : Aeneas.Std.Array U8 32#usize)
    (sign_bit : Bool)
    (h_repr : repr.as_bytes = ok bytes)
    (h_byter : sign_bit = (bytes[31]!.val.testBit 7))
     :
    spec (edwards.decompress.step_2 repr X Y Z) (fun result =>
      -- Y and Z are unchanged
      result.Y = Y ∧
      result.Z = Z ∧

      -- The sign bit is extracted from the compressed representation
      -- X is conditionally negated based on the sign bit
        (if sign_bit then
          (result.X = neg X)
        else
          result.X = X) ∧

        -- T = X' * Y
        (result.T = mul result.X Y )) := by
  sorry

end curve25519_dalek.edwards.CompressedEdwardsY
