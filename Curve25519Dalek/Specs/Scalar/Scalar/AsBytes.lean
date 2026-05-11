/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::as_bytes`

Extracts the little-endian `Array U8 32` byte representation of a `Scalar`.
The left-most byte is the least significant.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::as_bytes`**
• No panic (always returns successfully)
• The result equals the byte array stored in the scalar (`s.bytes`)
• Converting the result back to a `Scalar` via the constructor yields the original scalar
-/
@[step]
theorem as_bytes_spec (s : Scalar) :
    as_bytes s ⦃ (result : Array U8 32#usize) =>
      result = s.bytes ∧
      mk result = s ⦄ := by
  unfold as_bytes
  simp

end curve25519_dalek.scalar.Scalar
