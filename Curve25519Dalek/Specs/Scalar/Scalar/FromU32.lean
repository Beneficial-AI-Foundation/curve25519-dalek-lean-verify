/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `Scalar::from(u32)`

Specification and proof for `FromScalarU32::from`.

This function embeds a u32 into a Scalar by writing its little-endian bytes.

**Source**: curve25519-dalek/src/scalar.rs
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.scalar.FromScalarU32

/-
natural language description:

    • Creates a Scalar whose byte representation contains the little-endian
      encoding of x in the first four bytes and zeros elsewhere.

natural language specs:

    • The resulting scalar encodes the same numeric value as x
    • The function always succeeds (no panic)
-/

/-- **Spec and proof concerning `scalar.FromScalarU32.from`**:
- No panic (always returns successfully)
- The resulting Scalar encodes the value x
-/
@[progress]
theorem from_spec (x : U32) :
  «from» x ⦃ s => U8x32_as_Nat s.bytes = x.val ⦄ := by
  sorry

end curve25519_dalek.scalar.FromScalarU32
