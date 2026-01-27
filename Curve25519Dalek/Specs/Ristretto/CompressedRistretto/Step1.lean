/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Defs.Edwards.Representation

/-! # Spec Theorem for `ristretto.decompress.step_1`

Specification and proof for `ristretto.decompress.step_1`.

This function performs the first step of Ristretto decompression, validating
the encoding and extracting the field element s from the compressed representation.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.ristretto.decompress

/-
natural language description:

    • Takes a CompressedRistretto (32-byte array) c as input
    • Extracts the (identical) byte array representation b from the compressed point c
    • Parses the bytes in b into a field element s using from_bytes b
    • Converts s back to bytes b' via to_bytes s (which always produces canonical output in [0, p))
    • Performs constant-time equality check between b and b' to determine whether the original encoding b is canonical (i.e., whether U8x32_as_Nat(b) < p)
    • Checks if s is negative (i.e., if the least significant bit of b' is 1)

      Returns a tuple containing:

        - s_encoding_is_canonical: a Choice indicating whether the input byte encoding is canonical
          (i.e., whether U8x32_as_Nat(b) < p)
        - s_is_negative: a Choice indicating whether the least significant bit of b' is equal to 1
        - s: the field element extracted from the compressed representation

    This is the first validation step in Ristretto decompression. It ensures that:

    1. The input bytes b represent a canonical field element encoding (value in [0, p))
    2. The sign/negativity of the (canonicalised) field element is determined

natural language specs:

    • The function always succeeds (no panic) for any 32-byte input c
    • s_encoding_is_canonical is true if and only if U8x32_as_Nat(c) < p
    • s_is_negative is true if and only if (Field51_as_Nat s % p) % 2 = 1
    • The output field element s is valid (i.e., its limbs are appropriately bounded)

-/

/-- **Spec and proof concerning `ristretto.decompress.step_1`**:
    • The function always succeeds (no panic) for any 32-byte input `c`
    • s_encoding_is_canonical is true if and only if U8x32_as_Nat(c) < p
    • s_is_negative is true if and only if s is negative (LSB = 1)
    • The output field element s is valid (i.e., its limbs are appropriately bounded)
-/
@[progress]
theorem step_1_spec (c : CompressedRistretto) :
    ∃ (s_encoding_is_canonical s_is_negative : subtle.Choice) (s : backend.serial.u64.field.FieldElement51),

    step_1 c = ok (s_encoding_is_canonical, s_is_negative, s) ∧

    (s_encoding_is_canonical.val = 1#u8 ↔ U8x32_as_Nat c < p) ∧

    (s_is_negative.val = 1#u8 ↔ math.is_negative s.toField) ∧

    s.IsValid

    := by

  sorry

end curve25519_dalek.ristretto.decompress
