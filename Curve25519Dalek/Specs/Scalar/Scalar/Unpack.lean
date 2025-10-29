/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `Scalar::unpack`

Specification and proof for `Scalar::unpack`.

This function unpacks the element from a compact representation.

**Source**: curve25519-dalek/src/scalar.rs

## TODO
- Complete proof
-/

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
theorem unpack_spec (s : Scalar) :
    ∃ u,
    unpack s = ok u ∧
    pack u = ok s ∧
    Scalar52_as_Nat u = U8x32_as_Nat s.bytes
    := by
  sorry

end curve25519_dalek.scalar.Scalar
