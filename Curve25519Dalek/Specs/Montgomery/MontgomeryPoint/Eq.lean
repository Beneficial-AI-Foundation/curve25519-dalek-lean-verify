/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.CtEq

/-!
# Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::eq`

Checks equality of two `MontgomeryPoint` values by delegating to constant-time comparison:
• Compares the u-coordinates, decoded as `FieldElement51`, in constant time.
• Converts the resulting `Choice` to `Bool` via `FromBoolChoice`.

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint

/-- **Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::eq`**
• No panic (always returns successfully)
• Returns `true` iff the u-coordinates are equal modulo p
-/
@[step]
theorem eq_spec (self other : MontgomeryPoint) :
    eq self other ⦃ (b : Bool) =>
      (b = true ↔
        (U8x32_as_Nat self % 2 ^ 255) ≡ (U8x32_as_Nat other % 2 ^ 255) [MOD p]) ⦄ := by
  unfold eq
  step*
  unfold Bool.Insts.CoreConvertFromChoice.from
  simp only [spec, theta, wp_return]
  have key : decide (c.val = 1#u8) = true ↔ c = Choice.one := by
    cases c with
    | mk val valid =>
      simp [Choice.one]
  rw [key]
  exact c_post

end curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint
