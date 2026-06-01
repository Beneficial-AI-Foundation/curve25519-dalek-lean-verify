/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-!
# Spec theorem for `curve25519_dalek::edwards::CompressedEdwardsY::identity`

Returns the identity element of the Edwards curve as a `CompressedEdwardsY`
(a 32-byte array encoding the Y-coordinate in little-endian form).

The identity point on the twisted Edwards curve `ax² + y² = 1 + dx²y²` has
affine coordinates `(x, y) = (0, 1)`. When compressed, only the Y-coordinate
is stored (with the sign bit of `x` in the high bit of byte 31); since
`x = 0`, the sign bit is 0, so the little-endian encoding is
`[1, 0, 0, ..., 0]` (32 bytes).

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.CompressedEdwardsY.Insts.Curve25519_dalekTraitsIdentity

/-- **Spec theorem for `curve25519_dalek::edwards::CompressedEdwardsY::identity`**
• No panic (always returns successfully)
• The resulting `CompressedEdwardsY` encodes the value 1 (the Y-coordinate of the identity point)
-/
@[step]
theorem identity_spec :
    identity ⦃ (result : CompressedEdwardsY) =>
      U8x32_as_Nat result = 1 ⦄ := by
  unfold identity
  simp [U8x32_as_Nat, Array.make, Finset.sum_range_succ]

end curve25519_dalek.edwards.CompressedEdwardsY.Insts.Curve25519_dalekTraitsIdentity
