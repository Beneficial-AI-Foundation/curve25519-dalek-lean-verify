/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomerySquare
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.SquareMultiply

/-! # Spec Theorem for `Scalar52::montgomery_invert`

Specification and proof for `Scalar52::montgomery_invert`.

This function computes the multiplicative inverse using Montgomery form.

**Source**: curve25519-dalek/src/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek.backend.serial.u64.scalar curve25519_dalek.backend.serial.u64.scalar.Scalar52
namespace curve25519_dalek.scalar.Scalar52

/-
natural language description:

    • Takes as input an UnpackedScalar u that is assumed to be
      in Montgomery form. Then efficiently computes and returns an
      UnpackedScalar u' (also in Montgomery form) that represents
      the multiplicative inverse of u with respect to Montgomery multiplication.

    • This means: if we apply Montgomery multiplication to u and u',
      we get the Montgomery representation of 1, which is R mod L.

natural language specs:

    • For any UnpackedScalar u in Montgomery form with scalar_to_nat(u) ≢ 0 (mod L):
      - The function returns successfully with result u'
      - (Scalar52_as_Nat u * Scalar52_as_Nat u') mod L = R² mod L
      - This is equivalent to: montgomery_mul(u, u') = R mod L
-/

/-- **Spec and proof concerning `scalar.Scalar52.montgomery_invert`**:
- Precondition: u must be non-zero modulo L (i.e., represent a non-zero value in Montgomery form)
- No panic (always returns successfully for non-zero inputs)
- The result u' satisfies the property that Montgomery multiplication of u and u'
  yields R mod L (the Montgomery representation of 1)
-/
@[progress]
theorem montgomery_invert_spec (u : Scalar52) (h : Scalar52_as_Nat u % L ≠ 0)
    (h_bounds : ∀ i < 5, u[i]!.val < 2 ^ 62) :
    ∃ u', montgomery_invert u = ok u' ∧
    (Scalar52_as_Nat u * Scalar52_as_Nat u') % L = (R * R) % L := by
  unfold montgomery_invert

  progress as ⟨h1, h1_eq, h1_bnds⟩
  progress as ⟨h2, h2_eq, h2_bnds⟩


  sorry



end curve25519_dalek.scalar.Scalar52
