/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `MontgomeryPoint::to_bytes`

Specification and proof for `MontgomeryPoint::to_bytes`.

This function converts the structure to its byte representation.

**Source**: curve25519-dalek/src/montgomery.rs
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-
natural language description:

    • Convert a MontgomeryPoint to its byte representation.
      Since MontgomeryPoint is a type alias for Array U8 32#usize,
      this is an identity operation.

natural language specs:

    • to_bytes(mp) = mp (identity)
    • The function always succeeds (no panic)
-/

/-- **Spec and proof concerning `montgomery.MontgomeryPoint.to_bytes`**:
- No panic (always returns successfully)
- The result is the byte representation of the Montgomery point (identity)
-/
@[progress]
theorem to_bytes_spec (mp : MontgomeryPoint) :
    to_bytes mp ⦃ b => b = mp ⦄ := by
  unfold to_bytes
  simp

end curve25519_dalek.montgomery.MontgomeryPoint
