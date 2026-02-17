/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.ToBytes

/-! # Spec Theorem for `Scalar52::pack`

Specification and proof for `Scalar52::pack`.

This function packs the element into a compact representation.

Source: curve25519-dalek/src/scalar.rs
-/

open Aeneas.Std Result Aeneas.Std.WP curve25519_dalek.backend.serial.u64.scalar
namespace curve25519_dalek.scalar.Scalar52

/-
natural language description:

    • Takes an input UnpackedScalar r and returns
      the corresponding Scalar s.

natural language specs:

    • scalar_to_nat(s) = unpacked_scalar_to_nat(r)
    • unpack(s) = r
-/

/-- **Spec and proof concerning `scalar.Scalar52.pack`**:
- No panic (always returns successfully)
- Both the unpacked r and the packed s represent the same natural number modulo L
- The packed scalar is in canonical form (less than L) -/
@[progress]
theorem pack_spec (u : backend.serial.u64.scalar.Scalar52) :
    spec (pack u) (fun s =>
    U8x32_as_Nat s.bytes ≡ Scalar52_as_Nat u [MOD L] ∧
    U8x32_as_Nat s.bytes < L) := by
  unfold pack
  progress
  grind

end curve25519_dalek.scalar.Scalar52
