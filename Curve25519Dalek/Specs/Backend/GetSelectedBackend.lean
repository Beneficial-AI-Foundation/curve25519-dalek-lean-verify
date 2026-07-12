/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::backend::get_selected_backend`

Selects the computational backend used for scalar multiplication and multi-scalar operations.
In the full Rust implementation this function inspects CPU feature flags at runtime (AVX-512,
AVX-2) and picks the fastest available SIMD backend. Because the Lean extraction targets the
serial-only build (no `simd` cfg features), every conditional SIMD branch is compiled away and
the function unconditionally returns `BackendKind.Serial`.

Source: "curve25519-dalek/src/backend/mod.rs", lines 55–75
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend

/-- **Spec theorem for `curve25519_dalek::backend::get_selected_backend`**
• The function always succeeds (no panic)
• The result is `BackendKind.Serial`
-/
@[step]
theorem get_selected_backend_spec :
    get_selected_backend ⦃ (result : BackendKind) =>
      result = BackendKind.Serial ⦄ := by
  unfold get_selected_backend
  step*

end curve25519_dalek.backend
