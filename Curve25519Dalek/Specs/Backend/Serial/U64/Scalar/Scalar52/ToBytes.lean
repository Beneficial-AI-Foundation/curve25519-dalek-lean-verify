/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `Scalar52::to_bytes`

Specification and proof for `Scalar52::to_bytes`.

This function converts the structure to its byte representation.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes an unpacked scalar u (five 52-bit limbs stored in U64 values) and
      returns a 32-byte array b that represents the same 256-bit integer value modulo L
      in little-endian byte representation.

natural language specs:

    • u8x32_to_nat(b) ≡ scalar_to_nat(u) (mod L)
-/

/-- **Spec and proof concerning `scalar.Scalar52.to_bytes`**:
- No panic (always returns successfully)
- The result byte array represents the same number as the input unpacked scalar modulo L
-/
theorem to_bytes_spec (u : Scalar52) :
    ∃ b,
    to_bytes u = ok b ∧
    U8x32_as_Nat b ≡ Scalar52_as_Nat u [MOD L]
    := by
    sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
