/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `MontgomeryPoint::as_bytes`

Specification and proof for `MontgomeryPoint::as_bytes`.

This function converts the structure to its byte representation.

**Source**: curve25519-dalek/src/montgomery.rs
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-
natural language description:

    • Extract the byte representation of type [u8;32] from a MontgomeryPoint.
      Since MontgomeryPoint is a type alias for Array U8 32#usize,
      this is essentially an identity operation.

natural language specs:

    • as_bytes(mp) = mp (identity)
    • The function always succeeds (no panic)
-/

/-- **Spec and proof concerning `montgomery.MontgomeryPoint.as_bytes`**:
- No panic (always returns successfully)
- The result is the byte representation of the Montgomery point (identity)
-/
@[progress]
theorem as_bytes_spec (mp : MontgomeryPoint) :
    as_bytes mp ⦃ b => b = mp ⦄ := by
  unfold as_bytes
  simp

end curve25519_dalek.montgomery.MontgomeryPoint
