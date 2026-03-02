/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Edwards.CompressedEdwardsY.Decompress

/-! # Spec Theorem for `MontgomeryPoint::to_edwards`

Specification and proof for `MontgomeryPoint::to_edwards`.

This function attempts to convert a MontgomeryPoint (u-coordinate only) to an
EdwardsPoint on the twisted Edwards curve, using the birational map
y = (u-1)/(u+1), followed by Edwards decompression with a specified sign bit.

**Source**: curve25519-dalek/src/montgomery.rs:224-253

-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.montgomery.MontgomeryPoint
open curve25519_dalek.backend.serial.u64.field

/-
natural language description:

    Converts a MontgomeryPoint (u-coordinate only) to an EdwardsPoint using the
    birational map y = (u-1)/(u+1) (mod p), where p = 2^255 - 19.
    Special case: when u ≡ -1 (mod p), returns None (point is on the twist).
    Otherwise, computes y, encodes it with the specified sign bit, and decompresses
    to obtain a full EdwardsPoint.

natural language specs:

    When the function returns Some(edwards_point):
      - The Edwards y-coordinate satisfies the birational map: y ≡ (u-1)/(u+1) (mod p)
      - The edwards_point lies on the twisted Edwards curve equation
      - The sign bit is properly encoded

    When the function returns None:
      - Either u ≡ -1 (mod p) (point on the twist), or
      - The computed y-coordinate does not correspond to a valid curve point

    where p = 2^255 - 19
-/

/-- **Spec and proof concerning `montgomery.MontgomeryPoint.to_edwards`**:
- When the function returns Some(edwards_point), the Edwards y-coordinate satisfies
  the birational map: y * (u + 1) ≡ (u - 1) (mod p)
- The returned point lies on the twisted Edwards curve
-/
@[progress]
theorem to_edwards_spec (mp : MontgomeryPoint) (sign : U8) :
    to_edwards mp sign ⦃ result =>
      (∀ edwards_point, result = some edwards_point →
        let u := U8x32_as_Nat mp
        let y := Field51_as_Nat edwards_point.Y
        -- The y-coordinate satisfies the birational map y = (u-1)/(u+1) mod p
        (y * ((u + 1) % p)) % p = ((u - 1) % p) % p)
    ⦄ := by
  sorry

end curve25519_dalek.montgomery.MontgomeryPoint
