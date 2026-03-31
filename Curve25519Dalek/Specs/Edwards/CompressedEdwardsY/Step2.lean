/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI Assistant
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Edwards.CompressedEdwardsY.AsBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign
/-! # Spec Theorem for `CompressedEdwardsY::decompress::step_2`

Specification and proof for the second step of `CompressedEdwardsY::decompress`.

This function performs the final decompression step which:
1. Extracts the sign bit from the compressed representation (byte 31, bit 7)
2. Conditionally negates the x-coordinate according to the sign bit
3. Computes T = X * Y
4. Returns the complete EdwardsPoint in extended coordinates (X, Y, Z, T)

Ported from the Verus spec in dalek-lite/curve25519-dalek/src/edwards.rs (lines 507-539),
which asserts: result.X = if sign then field_neg(X) else X, result.T = field_mul(result.X, Y),
Y and Z unchanged, limb bounds 52-bit.

**Source**: curve25519-dalek/src/edwards.rs, lines 230-248
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51
open curve25519_dalek.backend.serial.u64.field

namespace curve25519_dalek.edwards.CompressedEdwardsY

/-
Natural language description:

    - Takes a CompressedEdwardsY and field elements X, Y, Z from step_1
    - Extracts the sign bit from the high bit of byte 31 of the compressed representation
    - Since sqrt_ratio_i returns the nonnegative square root, conditionally negates X
      according to the sign bit to match the encoded sign
    - Computes T = X * Y (the product of x and y coordinates)
    - Returns an EdwardsPoint with coordinates (X, Y, Z, T)

Natural language specs (ported from Verus):

    - The function always succeeds (no panic) given bounded inputs
    - result.X.toField = if sign_bit then -X.toField else X.toField
    - result.T.toField = result.X.toField * Y.toField
    - Y and Z are unchanged
    - Output bounds: result.X limbs ≤ 2^53-1, result.T limbs < 2^52
-/

/-- **Spec for `edwards.decompress.step_2`** (ported from Verus):
- No panic (always returns successfully given bounded inputs)
- Returns an EdwardsPoint with coordinates (X', Y, Z, T) where:
  - Y and Z are unchanged from the inputs
  - X'.toField = if sign_bit then -X.toField else X.toField
  - X' limbs ≤ 2^53 - 1
  - T.toField = X'.toField * Y.toField
  - T limbs < 2^52
-/
@[step]
theorem step_2_spec
    (repr : edwards.CompressedEdwardsY)
    (X : backend.serial.u64.field.FieldElement51)
    (Y : backend.serial.u64.field.FieldElement51)
    (Z : backend.serial.u64.field.FieldElement51)
    (bytes : Aeneas.Std.Array U8 32#usize)
    (sign_bit : Bool)
    (h_repr : repr.as_bytes = ok bytes)
    (h_byter : sign_bit = (bytes[31]!.val.testBit 7))
    (hX : ∀ i < 5, X[i]!.val ≤ 2 ^ 53 - 1)
    (hY : ∀ i < 5, Y[i]!.val < 2 ^ 51) :
    edwards.decompress.step_2 repr X Y Z ⦃ result =>
      result.Y = Y ∧
      result.Z = Z ∧
      (if sign_bit then
        result.X.toField = -X.toField
      else
        result.X = X) ∧
      (∀ i < 5, result.X[i]!.val ≤ 2 ^ 53 - 1) ∧
      result.T.toField = result.X.toField * Y.toField ∧
      (∀ i < 5, result.T[i]!.val < 2 ^ 52) ⦄ := by
  sorry

end curve25519_dalek.edwards.CompressedEdwardsY
