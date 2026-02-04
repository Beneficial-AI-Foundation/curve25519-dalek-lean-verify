/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Defs.Edwards.Representation

/-! # Spec Theorem for `CompressedRistretto::decompress`

Specification and proof for `CompressedRistretto::decompress`.

This function implements the Ristretto decompression (DECODE) function, which attempts to
decode a (valid) 32-byte representation back to a RistrettoPoint. The function is defined in the

- [Ristretto specification](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-08#section-4.3.1).

It takes a CompressedRistretto (a 32-byte array) and attempts to produce the associated RistrettoPoint,
returning None if the input byte array is not a valid canonical encoding.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.ristretto.CompressedRistretto

/-
natural language description:

Takes a CompressedRistretto (a 32-byte array) and attempts to decompress it to a
RistrettoPoint according to the Ristretto DECODE function specified in:

https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-08#section-4.3.1

Returns none if the input is not a valid canonical encoding.

natural language specs:

- The function always succeeds for all U8x32 input arrays (no panic)
- If the input is not valid, then the output is none
- If the input is valid, then the output is a valid Ristretto point that reflects the
  output of the pure mathematical decompression function
-/

/-- **Spec and proof concerning `ristretto.CompressedRistretto.decompress`**:
- The function always succeeds for all U8x32 input arrays (no panic)
- If the input is not valid, then the output is none
- If the input is valid, then the output is a valid Ristretto point that reflects the
  output of the pure mathematical decompression function
-/
theorem decompress_spec (comp : CompressedRistretto) :
    ∃ result, decompress comp = ok result ∧
    (¬comp.IsValid →
      result = none) ∧
    (comp.IsValid →
        ∃ rist,
        result = some rist ∧
        RistrettoPoint.IsValid rist ∧
        math.decompress_pure (U8x32_as_Nat comp) = some rist.toPoint) := by
  sorry

end curve25519_dalek.ristretto.CompressedRistretto
