/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Pack
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.FromBytes
/-! # Spec Theorem for `Scalar::unpack`

Specification and proof for `Scalar::unpack`.

This function unpacks the element from a compact representation.

**Source**: curve25519-dalek/src/scalar.rs

-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result curve25519_dalek.scalar.Scalar52
namespace curve25519_dalek.scalar.Scalar

/-
natural language description:

    • Takes an input Scalar s and returns the corresponding
      UnpackedScalar u.

natural language specs:

    • pack(u) = s
    • scalar_to_nat(s) = unpacked_scalar_to_nat(u)
-/

/-- **Spec and proof concerning `scalar.Scalar.unpack`**:
- No panic (always returns successfully)
- Packing the result back yields the original scalar: pack(u) = s
- Both the packed s and the unpacked u represent the same natural number
-/
@[progress]
theorem unpack_spec (s : Scalar) :
    unpack s ⦃ u =>
      Scalar52_as_Nat u = U8x32_as_Nat s.bytes ∧
      (∀ i < 5, u[i]!.val < 2 ^ 62) ⦄ := by
  sorry

end curve25519_dalek.scalar.Scalar
