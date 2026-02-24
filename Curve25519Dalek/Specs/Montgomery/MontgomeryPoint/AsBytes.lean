/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec Theorem for `MontgomeryPoint::as_bytes`

Specification and proof for `curve25519_dalek::montgomery::MontgomeryPoint::as_bytes`.

This function returns a reference to the internal 32-byte array representation
of a MontgomeryPoint.

**Source**: dalek-lite/curve25519-dalek/src/montgomery.rs, lines 459:4-464:5

## Natural Language Description

• Returns a reference to the internal byte array representation of the MontgomeryPoint
• The function is a const fn, meaning it can be evaluated at compile time
• In Lean, since MontgomeryPoint is defined as Array U8 32, this is essentially an identity function

## Natural Language Specs

• The function always succeeds (no panic conditions)
• Returns the exact same byte array that represents the MontgomeryPoint
• The result is a reference to the internal representation (in Rust terms)
• Mathematical property: bytesToField(result) = bytesToField(self)
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-- **Spec and proof for `montgomery.MontgomeryPoint.as_bytes`**:

Since MontgomeryPoint is defined as Array U8 32 in Lean, as_bytes returns the input unchanged.

Formal specification:
- The function always succeeds
- Returns the input unchanged (result = self)
- Preserves the field element representation
-/
@[progress]
theorem as_bytes_spec (mp : montgomery.MontgomeryPoint) :
    montgomery.MontgomeryPoint.as_bytes mp ⦃ result =>
    result = mp ⦄ := by
  unfold montgomery.MontgomeryPoint.as_bytes
  simp

end curve25519_dalek.montgomery.MontgomeryPoint
