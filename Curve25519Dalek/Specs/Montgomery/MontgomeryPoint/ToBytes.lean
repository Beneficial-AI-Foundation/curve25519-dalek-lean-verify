/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec Theorem for `MontgomeryPoint::to_bytes`

Specification and proof for `curve25519_dalek::montgomery::MontgomeryPoint::to_bytes`.

This function converts a MontgomeryPoint to its 32-byte array representation.

**Source**: dalek-lite/curve25519-dalek/src/montgomery.rs, lines 467:4-472:5

## Natural Language Description

• Converts the MontgomeryPoint to a 32-byte array
• The function is a const fn, meaning it can be evaluated at compile time
• In Lean, since MontgomeryPoint is defined as Array U8 32, this returns the array directly
• The difference from as_bytes is that this returns an owned array (not a reference in Rust terms)

## Natural Language Specs

• The function always succeeds (no panic conditions)
• Returns the exact byte array that represents the MontgomeryPoint
• The result is an owned copy of the internal representation (in Rust terms)
• Mathematical property: bytesToField(result) = bytesToField(self)
-/

open Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-- **Spec and proof for `montgomery.MontgomeryPoint.to_bytes`**:

Since MontgomeryPoint is defined as Array U8 32 in Lean, to_bytes returns the input unchanged.

Formal specification:
- The function always succeeds
- Returns the input unchanged (result = self)
- Preserves the field element representation
-/
@[progress]
theorem to_bytes_spec (mp : montgomery.MontgomeryPoint) :
    spec (montgomery.MontgomeryPoint.to_bytes mp) (fun result =>
    result = mp) := by
  unfold montgomery.MontgomeryPoint.to_bytes
  simp

end curve25519_dalek.montgomery.MontgomeryPoint
