/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # Spec Theorem for `Scalar::invert`

Specification and proof for `Scalar::invert`.

This function computes the multiplicative inverse.

**Source**: curve25519-dalek/src/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.scalar.Scalar

/-
natural language description:

    • Takes an input Scalar s and returns another Scalar s' that
      represents the multiplicative inverse of s within the underlying
      field \mathbb{Z} / \ell \mathbb{Z}.

natural language specs:

    • \forall Scalars s with s ≠ 0:
      scalar_to_nat(s) * scalar_to_nat(s') is congruent to 1 (mod \ell)
-/

/-- **Spec and proof concerning `scalar.Scalar.invert`**:
- Precondition: The input scalar s must be non-zero (inverting zero has undefined behavior)
- No panic (returns successfully for non-zero input)
- The result s' satisfies the multiplicative inverse property:
  U8x32_as_Nat(s.bytes) * U8x32_as_Nat(s'.bytes) ≡ 1 (mod L)
-/
theorem invert_spec (s : Scalar) (h : s ≠ ZERO) :
    ∃ s',
    invert s = ok s' ∧
    (U8x32_as_Nat s.bytes * U8x32_as_Nat s'.bytes) ≡ 1 [MOD L]
    := by
  sorry

end curve25519_dalek.scalar.Scalar
