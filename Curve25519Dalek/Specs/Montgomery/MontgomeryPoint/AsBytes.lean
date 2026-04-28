/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-!
# Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::as_bytes`

• Returns a reference to the internal byte array representation of the `MontgomeryPoint`
• The function is a `const fn`, meaning it can be evaluated at compile time
• In Lean, since `MontgomeryPoint` is defined as `Array U8 32`, this is essentially the identity

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-- **Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::as_bytes`**
• The function always succeeds (no panic conditions)
• Returns the exact same byte array that represents the `MontgomeryPoint`
-/
@[step]
theorem as_bytes_spec (self : MontgomeryPoint) :
    as_bytes self ⦃ (result : MontgomeryPoint) =>
      result = self ⦄ := by
  unfold as_bytes
  simp

end curve25519_dalek.montgomery.MontgomeryPoint
