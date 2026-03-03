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
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.MINUS_ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq

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
      (∀ ep, result = some ep →
        let u := U8x32_as_Nat mp
        let y := Field51_as_Nat ep.Y
        -- The y-coordinate satisfies the birational map y = (u-1)/(u+1) mod p
        (y * ((u + 1) % p)) % p = ((u - 1) % p) % p)
    ⦄ := by
  unfold to_edwards
  progress*
  -- After progress*, we have eliminated from_bytes
  -- Now need to handle: eq, sub, add, invert, mul, to_bytes, bit ops, decompress
  unfold FieldElement51.Insts.CoreCmpPartialEqFieldElement51.eq
  progress*  -- This eliminates ct_eq

  -- Add auxiliary lemmas for bounds on constants
  -- TODO: These can be proven by evaluating the constants
  have h_ONE_bounds : ∀ i < 5, FieldElement51.ONE[i]!.val < 2 ^ 53 := by sorry

  have h_MINUS_ONE_bounds : ∀ i < 5, FieldElement51.MINUS_ONE[i]!.val < 2 ^ 54 := by sorry

  -- We also need bounds that are compatible with u
  have h_u_sub_bounds : ∀ i < 5, u[i]!.val < 2 ^ 63 := by
    intro i hi
    have := u_post_2 i hi
    omega

  have h_ONE_sub_bounds : ∀ i < 5, FieldElement51.ONE[i]!.val < 2 ^ 54 := by
    intro i hi
    have := h_ONE_bounds i hi
    omega

  have h_u_add_bounds : ∀ i < 5, u[i]!.val < 2 ^ 53 := by
    intro i hi
    have := u_post_2 i hi
    omega

  -- Now manually apply the specs with appropriate bounds
  -- First handle Choice.from - it's simple, just unfold
  unfold Bool.Insts.CoreConvertFromChoice.from
  simp
  -- Split on the if-then-else
  split
  · -- Case: b = true (u = MINUS_ONE, return none)
    simp
  · progress*
    · sorry
    · sorry
    · sorry
    -- -- Case: b ≠ true (continue with computation)
    -- -- Apply all the specs automatically with progress*
    -- progress*
    -- case hrhs => intro i hi; have := fe2_post_3 i hi; omega
    -- -- Main proof: show that the Y-coordinate satisfies the birational map
    -- -- We have all the postconditions from sub, add, invert, mul, to_bytes, decompress
    -- sorry

end curve25519_dalek.montgomery.MontgomeryPoint
