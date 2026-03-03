/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.ExternallyVerified

/-! # Spec Theorem for `CompressedEdwardsY::decompress`

Specification and proof for `CompressedEdwardsY::decompress`.

Attempts to decompress a 32-byte array to an EdwardsPoint in extended twisted
Edwards coordinates. The compressed representation encodes a y-coordinate in the low 255 bits
and the sign (parity) of the x-coordinate in the high bit of byte 31. Decompression involves:

1. Extracting the y-coordinate from the byte array
2. Computing the (absolute value of the) x-coordinate using the curve equation $ax^2 + y^2 = 1 + dx^2y^2$
3. Adjusting the sign of x based on the encoded sign bit

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.CompressedEdwardsY

/-
Natural language description:

    - Decompresses a CompressedEdwardsY (U8x32 byte array) to an EdwardsPoint in extended coordinates
    - Extracts the y-coordinate from bytes 0-30 and the low 7 bits of byte 31 (little-endian)
    - Extracts the sign bit from the high bit of byte 31
    - Computes x from y using the curve equation: given y, solve for x² in ax² + y² = 1 + dx²y²
    - Adjusts the sign of x to match the encoded sign bit
    - Returns "ok none" if the input array does not encode a valid Edwards point, otherwise returns "ok some edwards_point"

Natural language specs:

    - The function always succeeds (no panic)
    - If the function does not return none, but Some(ep) with ep = (X, Y, Z, T), then:
      - The pair (x,y) fulfils the curve equation ax² + y² = 1 + dx²y² (mod p), whereby x = X/Z and y = Y/Z
      - y equals the y-coordinate encoded in the input byte array
      - The sign (parity) of x matches the high bit of byte 31 in the input byte array
      - T = X * Y
-/

/-- **Spec and proof concerning `edwards.CompressedEdwardsY.decompress`**:
- No panic (always returns successfully)
- If the function returns Some(ep) with ep = (X, Y, Z, T), then:
  - The affine coordinates (x,y) where x = X/Z and y = Y/Z satisfy the curve equation
    ax² + y² = 1 + dx²y² (mod p)
  - y equals the y-coordinate encoded in the input byte array (bytes 0-30 and low 7 bits of byte 31)
  - The sign (parity) of x matches the high bit of byte 31 in the input byte array
  - T = X * Y (mod p)
-/
@[externally_verified, progress] -- proven in Verus
theorem decompress_spec (cey : edwards.CompressedEdwardsY) :
    edwards.CompressedEdwardsY.decompress cey ⦃ result =>

      (∀ ep, result = some ep →
        let y_encoded := (U8x32_as_Nat cey) % (2^255)
        let x_sign_bit := cey[31]!.val.testBit 7

        (∃ Z_inv x_val y_val x_is_neg,
          field.FieldElement51.invert ep.Z = ok Z_inv ∧
          (Field51_as_Nat ep.X * Field51_as_Nat Z_inv) % p = x_val ∧
          (Field51_as_Nat ep.Y * Field51_as_Nat Z_inv) % p = y_val ∧
          field.FieldElement51.is_negative ep.X = ok x_is_neg ∧

          (y_val * y_val % p = (x_val * x_val + 1 + d * x_val * x_val * y_val * y_val) % p) ∧

          y_val % p = y_encoded % p ∧

          (x_sign_bit ↔ x_is_neg.val = 1#u8) ∧

          (Field51_as_Nat ep.T % p = (Field51_as_Nat ep.X * Field51_as_Nat ep.Y) % p))) ⦄ := by
  sorry

end curve25519_dalek.edwards.CompressedEdwardsY
