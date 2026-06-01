/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Pack
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.FromBytes

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::unpack`

Takes an input `Scalar` `self` and unpacks it from its compact byte representation,
returning the corresponding `Scalar52` `u`.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.scalar.Scalar52 curve25519_dalek.backend.serial.u64.scalar
namespace curve25519_dalek.scalar.Scalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::unpack`**
• No panic (always returns `Ok`)
• The natural number value is preserved: `Scalar52_as_Nat u = U8x32_as_Nat self.bytes`
• Each limb satisfies the 52-bit bound: `∀ i < 5, u[i]!.val < 2 ^ 52`
-/
@[step]
theorem unpack_spec (self : Scalar) :
    unpack self ⦃ (u : Scalar52) =>
      Scalar52_as_Nat u = U8x32_as_Nat self.bytes ∧
      ∀ i < 5, u[i]!.val < 2 ^ 52 ⦄ := by
  unfold unpack
  step*

end curve25519_dalek.scalar.Scalar
