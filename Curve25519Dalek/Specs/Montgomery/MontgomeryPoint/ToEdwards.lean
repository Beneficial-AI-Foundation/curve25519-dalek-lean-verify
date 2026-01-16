/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `MontgomeryPoint::to_edwards`

Specification and proof for `MontgomeryPoint::to_edwards`.

This function attempts to convert a MontgomeryPoint (only the u-coordinate) to an
EdwardsPoint on the twisted Edwards curve, using the birational map
y = (u-1)/(u+1), followed by Edwards decompression with a specified sign bit given as an additional input.

**Source**: curve25519-dalek/src/montgomery.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-
natural language description:

• Converts a MontgomeryPoint (u-coordinate only) to an EdwardsPoint
  using the birational map:
  - y ≡ (u-1)/(u+1) (mod p)

• The generated y-coordinate is combined with the input sign parameter and subsequently
  decompressed to obtain a full EdwardsPoint.

• Special case: when u = -1, the denominator is zero.
  The function returns None in this case.

natural language specs:

• The function returns None if u ≡ -1 (mod p)
• Otherwise, returns an EdwardsPoint where:
  - The y-coordinate satisfies: y * (u + 1) ≡ (u-1) (mod p)
  - The sign of x matches the input sign parameter
where p = 2^255 - 19
-/

/-- **Spec and proof concerning `montgomery.MontgomeryPoint.to_edwards`**:
- Returns None if u ≡ -1 (mod p)
- Returns None if the y-coordinate cannot be decompressed to a valid Edwards point
- Otherwise, returns Some(EdwardsPoint) where:
  - The y-coordinate satisfies: y * (u + 1) ≡ (u-1) (mod p)
  - The sign of x matches the input sign parameter
where p = 2^255 - 19
-/
@[progress]
theorem to_edwards_spec (mp : MontgomeryPoint) (sign : U8) :
    to_edwards mp sign ⦃ opt_e =>
      let u := U8x32_as_Nat mp;
      ((u + 1) % p = 0 → opt_e = none) ∧
      ((u + 1) % p ≠ 0 →
        (opt_e = none ∨ -- can still return none if y cannot be decompressed into a valid Edwards point
          ∃ e x_sign,
            opt_e = some e ∧
            field.FieldElement51.is_negative e.X = ok x_sign ∧
            (let y := Field51_as_Nat e.Y; y * (u + 1) % p = (u - 1) % p) ∧
            (x_sign.val = 1#u8 ↔ sign.val.testBit 0))) ⦄ := by
  sorry

end curve25519_dalek.montgomery.MontgomeryPoint
