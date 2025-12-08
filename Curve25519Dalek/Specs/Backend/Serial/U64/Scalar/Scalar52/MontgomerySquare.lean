/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.SquareInternal
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce
/-! # Spec Theorem for `Scalar52::montgomery_square`

Specification and proof for `Scalar52::montgomery_square`.

This function performs Montgomery squaring.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes as input an UnpackedScalar m that is assumed to be in Montgomery form.
      Then computes and returns an UnpackedScalar w (also in Montgomery form)
      that represents the Montgomery square of m,
      i.e., w = MontgomeryMul(m,m) = (m * m * R⁻¹) mod L.

natural language specs:

    • For any UnpackedScalar m in Montgomery form:
      - (Scalar52_as_Nat m * Scalar52_as_Nat m) mod L = (Scalar52_as_Nat w * R) mod L
-/

/-- **Spec and proof concerning `scalar.Scalar52.montgomery_square`**:
- No panic (always returns successfully)
- The result w satisfies the Montgomery squaring property:
  (m * m) ≡ w * R (mod L), where R = 2^260 is the Montgomery constant
-/
@[progress]
theorem montgomery_square_spec (m : Scalar52)  (hm : ∀ i < 5, m[i]!.val < 2 ^ 62):
    ∃ w,
    montgomery_square m = ok w ∧
    (Scalar52_as_Nat m * Scalar52_as_Nat m) % L = (Scalar52_as_Nat w * R) % L
    := by
  unfold montgomery_square
  progress*

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
