/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `CompressedRistretto::as_bytes`

Specification and proof for `CompressedRistretto::as_bytes`.

This function converts the structure to its byte representation.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.ristretto.CompressedRistretto

/-
natural language description:

    • Extract the byte representation of type [u8;32] from a CompressedRistretto cr.
      Since CompressedRistretto is defined as a type alias for Array U8 32#usize,
      this is essentially an identity operation that returns the underlying byte array.

natural language specs:

    • as_bytes(cr) = cr, i.e., the function is the identity operation
    • The operation never panics (always returns successfully)
-/

/-- **Spec and proof concerning `ristretto.CompressedRistretto.as_bytes`**:
- No panic (always returns successfully)
- The result is the byte representation of the compressed Ristretto point
- Since CompressedRistretto is defined as Array U8 32#usize, as_bytes is essentially the identity
-/
theorem as_bytes_spec (cr : CompressedRistretto) :
    ∃ b,
    as_bytes cr = ok b ∧
    b = cr
    := by
  unfold as_bytes
  simp

end curve25519_dalek.ristretto.CompressedRistretto
