/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.ToBytes

/-! # Spec Theorem for `Scalar52::pack`

This function packs the element into a compact representation.

Source: curve25519-dalek/src/scalar.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek.backend.serial.u64.scalar
  curve25519_dalek.backend.serial.u64.scalar
namespace curve25519_dalek.scalar.Scalar52

/-
natural language description:

    • Takes an input UnpackedScalar r and returns
      the corresponding Scalar s.

natural language specs:

    • scalar_to_nat(s) = unpacked_scalar_to_nat(r)
    • unpack(s) = r
-/

/-- **Spec theorem for `scalar.Scalar52.pack`**:
- Both the unpacked r and the packed s represent the same natural number modulo L
- The packed scalar is in canonical form (less than L) -/
@[step]
theorem pack_spec (self : Scalar52) (h : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (h' : Scalar52_as_Nat self < L) :
    pack self ⦃ (result : Scalar) =>
      U8x32_as_Nat result.bytes ≡ Scalar52_as_Nat self [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold pack
  step*
  exact ⟨by simp only [*, Nat.ModEq], by assumption⟩

end curve25519_dalek.scalar.Scalar52
