/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Scalar.Scalar.Reduce

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::from_bytes_mod_order`

Constructs a `Scalar` from a `[u8; 32]` byte array by reducing the byte array
(as a natural number) modulo the group order ℓ, returning the canonical reduced scalar.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::from_bytes_mod_order`**
• The function always succeeds (no panic)
• The result scalar (as nat) is congruent to the input bytes (as nat) modulo L
• The result scalar is strictly less than L (the group order)
-/
@[step]
theorem from_bytes_mod_order_spec (bytes : Array U8 32#usize) :
    from_bytes_mod_order bytes ⦃ (s : Scalar) =>
      U8x32_as_Nat s.bytes ≡ U8x32_as_Nat bytes [MOD L] ∧
      U8x32_as_Nat s.bytes < L ⦄ := by
  unfold from_bytes_mod_order Insts.CoreOpsIndexIndexUsizeU8.index
  step*
  have := high_bit_zero_of_lt_L s.bytes
  simp [*] at *
  grind

end curve25519_dalek.scalar.Scalar
