/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::to_bytes`

Takes an input `Scalar` `s` and returns its constituting byte array `a` of type `[u8; 32]`.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::to_bytes`**
• No panic (always returns successfully)
• The result array `a` equals the byte array stored in the scalar (`s.bytes`)
• Converting the result `a` back to a `Scalar` via the constructor yields the original scalar `s`
-/
@[step]
theorem to_bytes_spec (s : Scalar) :
    to_bytes s ⦃ (a : Array U8 32#usize) =>
      a = s.bytes ∧
      mk a = s ⦄ := by
  unfold to_bytes
  simp

end curve25519_dalek.scalar.Scalar
