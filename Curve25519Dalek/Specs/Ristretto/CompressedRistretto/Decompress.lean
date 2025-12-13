/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs.Edwards.Representation

/-! # Spec Theorem for `CompressedRistretto::decompress`

Specification and proof for `CompressedRistretto::decompress`.

This function implements the Ristretto decompression (DECODE) function, which attempts to
decode a (valid) 32-byte representation back to a RistrettoPoint. The function is defined in the

- [Ristretto specification](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-08#section-4.3.1).

It takes a CompressedRistretto (a 32-byte array) and attempts to produce a RistrettoPoint,
returning None if the input is not a valid canonical encoding.

**Source**: curve25519-dalek/src/ristretto.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.curve_models (ProjectivePoint)
namespace curve25519_dalek.ristretto.CompressedRistretto

/-
natural language description:

Takes a CompressedRistretto (a 32-byte array) and attempts to decompress it to a
RistrettoPoint according to the Ristretto DECODE function specified in:

https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-08#section-4.3.1

Returns None if the input is not a valid canonical encoding.

natural language specs:

- The function always succeeds for all U8x32 input arrays (no panic)
- If the output is not None, then it is a valid Ristretto point, i.e., it fulfils the Edwards point curve equation
- If the output is not None, then compressing the output Ristretto point gives back the original input byte array
-/

/-- **Spec and proof concerning `ristretto.CompressedRistretto.decompress`**:
- The function always succeeds (no panic)
- If the output is not None, then it is a valid Ristretto point, i.e., it fulfils the Edwards point curve equation
- If the output is not None, then compressing the output Ristretto point gives back the original input byte array
-/
theorem decompress_spec
  (comp : CompressedRistretto) :

  ∃ result, decompress comp = ok result ∧

    ((result = none) ∨

    (∃ rist,
      result = some rist ∧
      RistrettoPoint.compress rist = ok comp ∧
      (∃ proj,
        edwards.EdwardsPoint.as_projective rist = ok proj ∧
        ProjectivePoint.IsValid proj))) := by
  sorry

end curve25519_dalek.ristretto.CompressedRistretto
