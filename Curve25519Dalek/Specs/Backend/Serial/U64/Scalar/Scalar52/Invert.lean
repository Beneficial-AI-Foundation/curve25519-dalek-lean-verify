/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `Scalar52::invert`

Specification and proof for `Scalar52::invert`.

This function computes the multiplicative inverse.

**Source**: curve25519-dalek/src/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek.backend.serial.u64.scalar curve25519_dalek.backend.serial.u64.scalar.Scalar52
namespace curve25519_dalek.scalar.Scalar52

/-
natural language description:

    • Takes as input an UnpackedScalar u and returns another UnpackedScalar u’ that
      represents the multiplicative inverse of u within the underlying
      field \mathbb{Z} / \ell \mathbb{Z}. This is done by first
      converting u into Montgomery form, then inverting with
      montgomery_invert, and then converting back into UnpackedScalar.

natural language specs:

    • \forall UnpackedScalars u with u ≠ 0:
      scalar_to_nat(u) * scalar_to_nat(u') is congruent to 1 (mod \ell)
-/

/-- **Spec and proof concerning `scalar.Scalar52.invert`**:
- Precondition: The unpacked input scalar u must be non-zero (inverting zero has undefined behavior)
- No panic (returns successfully for non-zero input)
- The result u' satisfies the multiplicative inverse property:
  Scalar52_as_Nat(u) * Scalar52_as_Nat(u') ≡ 1 (mod L)
-/
theorem invert_spec (u : Scalar52) (h : u ≠ ZERO) :
    ∃ u',
    invert u = ok u' ∧
    (Scalar52_as_Nat u * Scalar52_as_Nat u') ≡ 1 [MOD L]
    := by
  sorry

end curve25519_dalek.scalar.Scalar52
