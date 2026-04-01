/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.ExternallyVerified
/-! # Spec Theorem for `CompressedEdwardsY::decompress`

Specification and proof for `CompressedEdwardsY::decompress`.

Attempts to decompress a 32-byte array to an EdwardsPoint in extended twisted
Edwards coordinates. The compressed representation encodes a y-coordinate in the low 255 bits
and the sign (parity) of the x-coordinate in the high bit of byte 31. Decompression involves:

1. Extracting the y-coordinate from the byte array
2. Computing the (absolute value of the) x-coordinate using the curve equation ax² + y² = 1 + dx²y²
3. Adjusting the sign of x based on the encoded sign bit

Ported from the Verus spec in dalek-lite/curve25519-dalek/src/edwards.rs (lines 277-299),
which asserts: is_valid_y ↔ is_some, well-formed point, Y = from_bytes, Z = 1, sign matching.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field
open Edwards

namespace curve25519_dalek.edwards.CompressedEdwardsY

/-
Natural language description:

    - Decompresses a CompressedEdwardsY (U8x32 byte array) to an EdwardsPoint in
      extended coordinates
    - Extracts the y-coordinate from bytes 0-30 and the low 7 bits of byte 31 (little-endian)
    - Extracts the sign bit from the high bit of byte 31
    - Computes x from y using the curve equation: given y, solve for x² in -x² + y² = 1 + dx²y²
    - Adjusts the sign of x to match the encoded sign bit
    - Returns "ok none" if the input does not encode a valid Edwards point, otherwise "ok (some ep)"

Natural language specs (ported from Verus):

    - The function always succeeds (no panic)
    - Decompression succeeds (returns some) iff the y-coordinate is valid (a curve point exists)
    - When successful, the returned EdwardsPoint satisfies:
      - Y.toField = the y-coordinate encoded in the input bytes (mod p)
      - Z.toField = 1
      - The point is valid: ep.IsValid (curve equation, T = XY/Z, bounds, Z ≠ 0)
      - The sign of X matches the sign bit (when y² ≠ 1 in the field)
-/

/-- **Spec for `edwards.CompressedEdwardsY.decompress`**:
- No panic (always returns successfully)
- Returns `none` iff the y-coordinate does not admit a curve point
- When returning `some ep`:
  - ep.IsValid (curve equation, T = XY/Z, bounds, Z ≠ 0)
  - Y.toField matches the encoded y-coordinate
  - Z.toField = 1
  - X sign matches bit 255 of the input (when y² ≠ 1)
-/
@[step, externally_verified] -- proven in Verus
theorem decompress_spec (cey : edwards.CompressedEdwardsY) :
    edwards.CompressedEdwardsY.decompress cey ⦃ result =>
      let y : CurveField := (U8x32_as_Nat cey % 2 ^ 255 : CurveField)
      let x_sign_bit := cey[31]!.val.testBit 7
      -- Decompression succeeds iff y is a valid Edwards y-coordinate
      (result.isSome ↔ ∃ pt : Point Ed25519, pt.y = y) ∧
      -- When successful:
      (∀ ep, result = some ep →
        -- is_well_formed_edwards_point
        ep.IsValid ∧
        -- Y matches the encoded y-coordinate (ZMod and Nat levels)
        ep.Y.toField = y ∧
        Field51_as_Nat ep.Y ≡ (U8x32_as_Nat cey % 2 ^ 255) [MOD p] ∧
        -- Z = 1 (ZMod and Nat levels)
        ep.Z.toField = 1 ∧
        Field51_as_Nat ep.Z % p = 1 ∧
        ep.T.toField = ep.X.toField * ep.Y.toField ∧
        -- X sign matches bit 255
        -- (when y² ≠ 1, i.e. the non-degenerate case where x ≠ 0)
        (y ^ 2 ≠ 1 →
          (x_sign_bit ↔ (Field51_as_Nat ep.X % p) % 2 = 1))) ⦄ := by
  sorry

end curve25519_dalek.edwards.CompressedEdwardsY
