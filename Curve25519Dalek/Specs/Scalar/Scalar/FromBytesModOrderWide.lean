/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.FromBytesWide
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Pack

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::from_bytes_mod_order_wide`

Converts a `[u8; 64]` byte array into a reduced `Scalar` modulo the group order ℓ.
The input bytes are interpreted as a 512-bit little-endian integer before reduction.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::from_bytes_mod_order_wide`**
• The function does not panic for any `[u8; 64]` input
• The result scalar s, when converted to nat, equals the input bytes converted to nat modulo L
• The result scalar s is less than L (the group order)
-/
@[step]
theorem from_bytes_mod_order_wide_spec (input : Array U8 64#usize) :
    from_bytes_mod_order_wide input ⦃ (result : Scalar) =>
      U8x32_as_Nat result.bytes ≡ U8x64_as_Nat input [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold from_bytes_mod_order_wide
  step*
  all_goals simp_all [Nat.ModEq]

end curve25519_dalek.scalar.Scalar
