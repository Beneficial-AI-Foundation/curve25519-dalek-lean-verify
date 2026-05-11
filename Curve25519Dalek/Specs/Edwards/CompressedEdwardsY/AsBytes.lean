/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::edwards::CompressedEdwardsY::as_bytes`

This function exposes the internal 32-byte little-endian encoding stored inside a
`CompressedEdwardsY`.

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.CompressedEdwardsY

/-- **Spec theorem for `curve25519_dalek::edwards::CompressedEdwardsY::as_bytes`**
• The function succeeds (always returns `ok`)
• The result is exactly the internal byte array representation
-/
@[step]
theorem as_bytes_spec (self : CompressedEdwardsY) :
    as_bytes self ⦃ (result : Array U8 32#usize) =>
      result = self ⦄ := by
  unfold as_bytes
  simp

end curve25519_dalek.edwards.CompressedEdwardsY
