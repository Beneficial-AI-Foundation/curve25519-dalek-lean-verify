/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-!
# Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::to_bytes`

• Converts the `MontgomeryPoint` to a 32-byte array
• The function is a `const fn`, meaning it can be evaluated at compile time
• In Lean, since `MontgomeryPoint` is defined as `Array U8 32`, this returns the array directly
• The difference from `as_bytes` is that this returns an owned array (not a reference in Rust terms)

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-- **Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::to_bytes`**
• The function always succeeds (no panic conditions)
• Returns the exact byte array that represents the `MontgomeryPoint`
-/
@[step]
theorem to_bytes_spec (self : MontgomeryPoint) :
    to_bytes self ⦃ (result : MontgomeryPoint) =>
      result = self ⦄ := by
  unfold to_bytes
  simp

end curve25519_dalek.montgomery.MontgomeryPoint
