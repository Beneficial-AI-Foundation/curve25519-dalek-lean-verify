/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `EdwardsPoint::to_montgomery`

Specification and proof for `EdwardsPoint::to_montgomery`.

This function converts an EdwardsPoint from the twisted Edwards curve to the
corresponding MontgomeryPoint (only the u-coordinate) on the Montgomery curve, using the birational map
u = (1+y)/(1-y) = (Z+Y)/(Z-Y).

**Source**: curve25519-dalek/src/edwards.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Converts an EdwardsPoint from extended twisted Edwards coordinates (X, Y, Z, T)
to a MontgomeryPoint (u-coordinate only), using the birational map:
  - u ≡ (1+y)/(1-y) ≡ (Z+Y)/(Z-Y) (mod p)

• Special case: when Y = Z (affine y = 1, the identity point on Edwards curve),
  the denominator is zero. Since 0.invert() = 0 in this implementation,
  this yields u = 0.

• The output u is represented as an U8x32 array (a type alias for MontgomeryPoint)

natural language specs:

• The function always succeeds (no panic)
• For the input Edwards point (X, Y, Z, T), the resulting MontgomeryPoint has u-coordinate:
  - If Z ≢ Y (mod p): u ≡ (Z+Y) * (Z-Y)^(-1) (mod p)
  - If Z ≡ Y (mod p): u ≡ 0 (mod p)
where p = 2^255 - 19
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.to_montgomery`**:
- No panic (always returns successfully)
- For the input Edwards point (X, Y, Z, T), the resulting MontgomeryPoint has u-coordinate:
  - If (Z-Y) ≢ 0 (mod p): u ≡ (Z+Y) * (Z-Y)^(-1) (mod p)
  - If (Z-Y) ≡ 0 (mod p): u ≡ 0 (mod p)
where p = 2^255 - 19
-/
@[progress]
theorem to_montgomery_spec (e : EdwardsPoint) :
    ∃ mp,
    to_montgomery e = ok mp ∧

    let Y := Field51_as_Nat e.Y
    let Z := Field51_as_Nat e.Z
    let u := U8x32_as_Nat mp

    if (Z - Y) % p = 0 then
      u % p = 0
    else
      u * (Z - Y) % p = (Z + Y) % p := by

    sorry

end curve25519_dalek.edwards.EdwardsPoint
