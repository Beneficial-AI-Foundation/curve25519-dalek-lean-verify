/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Ristretto.RistrettoPoint.CtEq

/-!
# Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::eq`

Checks equality of two Ristretto points by delegating to constant-time comparison:
• Calls `RistrettoPoint.ct_eq(self, other)` to obtain a `Choice`
• Converts the `Choice` to `Bool` via `From<Choice> for bool`
  (`Choice.one → true`, `Choice.zero → false`)

Source: "curve25519-dalek/src/ristretto.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreCmpPartialEqRistrettoPoint

/-- **Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::eq`**
• No panic (always returns successfully given valid inputs)
• Returns true iff the two points satisfy the multiplicative Ristretto equivalence condition:
  X1·Y2 ≡ Y1·X2 (mod p) or X1·X2 ≡ Y1·Y2 (mod p)
-/
@[step]
theorem eq_spec (self other : RistrettoPoint) (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    eq self other ⦃ (result : Bool) =>
      (result = true ↔
        (Field51_as_Nat self.X * Field51_as_Nat other.Y) ≡
          (Field51_as_Nat self.Y * Field51_as_Nat other.X) [MOD p] ∨
        (Field51_as_Nat self.X * Field51_as_Nat other.X) ≡
          (Field51_as_Nat self.Y * Field51_as_Nat other.Y) [MOD p]) ⦄ := by
  unfold eq
  step*
  unfold Bool.Insts.CoreConvertFromChoice.from
  simp only [spec, theta, wp_return]
  have key : decide (c.val = 1#u8) = true ↔ c = Choice.one := by
    cases c with | mk val valid => simp [Choice.one]
  rw [key]
  exact c_post

end curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreCmpPartialEqRistrettoPoint
