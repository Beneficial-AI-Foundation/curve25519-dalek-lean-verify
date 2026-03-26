/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs

/-! # Spec Theorem for `CompressedRistretto::identity`

Specification and proof for the `Identity` trait implementation for `CompressedRistretto`.

This function returns the identity element as a `CompressedRistretto`, which is a 32-byte
array of zeros.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.ristretto.CompressedRistretto.Insts.Curve25519_dalekTraitsIdentity

/-
natural language description:

- Returns the identity element for CompressedRistretto, which is 32 zero bytes

natural language specs:

- The function always succeeds (no panic)
- The resulting CompressedRistretto is 32 zero bytes
-/

/-- **Spec and proof concerning
`ristretto.CompressedRistretto.Insts.Curve25519_dalekTraitsIdentity.identity`**:
- No panic (always returns successfully)
- The resulting CompressedRistretto is 32 zero bytes
-/
@[progress]
theorem identity_spec :
    identity ⦃ (result : CompressedRistretto) =>
      ∀ i : Fin 32, result[i]! = 0#u8 ⦄ := by
  intro i
  fin_cases i <;> simp [Array.repeat]

end curve25519_dalek.ristretto.CompressedRistretto.Insts.Curve25519_dalekTraitsIdentity
