/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs

/-! # Spec Theorem for `CompressedRistretto::to_bytes`

Specification and proof for `CompressedRistretto::to_bytes`.

This function converts the CompressedRistretto type to its underlying byte representation.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.ristretto.CompressedRistretto

/-
natural language description:

    • Extract the byte representation of type [u8;32] from a CompressedRistretto.
      Since CompressedRistretto is defined as a type alias for Array U8 32#usize,
      this is essentially just an identity operation that returns the underlying byte array.

natural language specs:

    • The operation never panics (always returns successfully)
    • to_bytes(cr) = cr, i.e., the function is the identity operation
-/

/-- **Spec and proof concerning `ristretto.CompressedRistretto.to_bytes`**:
    • The operation never panics (always returns successfully)
    • to_bytes(cr) = cr, i.e., the function is the identity operation
-/
@[progress]
theorem to_bytes_spec (cr : CompressedRistretto) :
    to_bytes cr ⦃ b =>
    b = cr ⦄ := by
  unfold to_bytes
  simp

end curve25519_dalek.ristretto.CompressedRistretto
