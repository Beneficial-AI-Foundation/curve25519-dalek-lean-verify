/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs

/-! # as_bytes

Specification and proof for `CompressedEdwardsY::as_bytes`.

This function returns a reference to the internal 32-byte array representation.

Source: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result curve25519_dalek

namespace curve25519_dalek.edwards.CompressedEdwardsY

/-! ## Specification for `CompressedEdwardsY::as_bytes`-/

/-- **Spec for `edwards.CompressedEdwardsY.as_bytes`**:
- The function succeeds (always returns `ok`)
- The result is exactly the internal byte array representation. -/
theorem as_bytes_spec
    (self : edwards.CompressedEdwardsY) :
    ∃ result, as_bytes self = ok result ∧
    result = self := by
  unfold as_bytes
  simp

end curve25519_dalek.edwards.CompressedEdwardsY
