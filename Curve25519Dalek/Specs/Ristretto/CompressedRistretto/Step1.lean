/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `ristretto.decompress.step_1`

Specification and proof for `ristretto.decompress.step_1`.

This function performs the first step of Ristretto decompression, validating
the encoding and extracting the field element s from the compressed representation.

**Source**: curve25519-dalek/src/ristretto.rs, lines 277:4-295:5
-/

open Aeneas.Std Result
namespace curve25519_dalek.ristretto.decompress

/-
natural language description:

    • Takes a CompressedRistretto (32-byte array) as input
    • Extracts the byte array representation from the compressed point
    • Parses the bytes into a field element s using FieldElement51.from_bytes
    • Converts s back to bytes to check canonical encoding
    • Performs constant-time equality check between original bytes and re-encoded bytes
    • Checks if s is negative (i.e., if the least significant bit of the byte encoding is 1)
    • Returns a tuple containing:
        - s_encoding_is_canonical: a Choice indicating whether the encoding is canonical
        - s_is_negative: a Choice indicating whether s is negative
        - s: the field element extracted from the compressed representation

    This is the first validation step in Ristretto decompression. It ensures that:
    1. The input bytes represent a canonical field element encoding
    2. The sign/negativity of the field element is determined for later use

natural language specs:

    • The function always succeeds (no panic) for any 32-byte input
    • s_encoding_is_canonical is true iff the input bytes are the canonical encoding of s
    • s_is_negative is true iff the least significant bit of s's byte representation is 1
-/

/-- **Spec and proof concerning `ristretto.decompress.step_1`**:
    - The function always succeeds (no panic) for any 32-byte input
    - s_encoding_is_canonical is true iff the input bytes are the canonical encoding of s
    - s_is_negative is true iff the least significant bit of s's byte representation is 1
-/
@[progress]
theorem step_1_spec (repr : ristretto.CompressedRistretto) :
    ∃ (s_encoding_is_canonical s_is_negative : subtle.Choice)
      (s : backend.serial.u64.field.FieldElement51),
    step_1 repr = ok (s_encoding_is_canonical, s_is_negative, s) ∧

    -- The field element s is successfully parsed from the byte representation
    (∃ a, ristretto.CompressedRistretto.as_bytes repr = ok a ∧
     backend.serial.u64.field.FieldElement51.from_bytes a = ok s) ∧

    -- The canonicality check compares the original bytes with re-encoded bytes
    (∃ (s_bytes_check : Array U8 32#usize) (s1 s2 : Slice U8),
     backend.serial.u64.field.FieldElement51.to_bytes s = ok s_bytes_check ∧
     core.array.Array.index (core.ops.index.IndexSlice
       (core.slice.index.SliceIndexRangeFullSliceSlice U8)) s_bytes_check () = ok s1 ∧
     (∃ a, ristretto.CompressedRistretto.as_bytes repr = ok a ∧
      (↑(Array.to_slice a) : Result (Slice U8)) = ok s2) ∧
     subtle.ConstantTimeEqSlice.ct_eq subtle.ConstantTimeEqU8 s1 s2 = ok s_encoding_is_canonical) ∧

    -- The negativity check examines the field element
    field.FieldElement51.is_negative s = ok s_is_negative := by

  sorry

end curve25519_dalek.ristretto.decompress
