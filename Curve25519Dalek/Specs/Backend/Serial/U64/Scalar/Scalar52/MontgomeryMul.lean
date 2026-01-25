/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MulInternal
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce

/-! # Spec Theorem for `Scalar52::montgomery_mul`

Specification and proof for `Scalar52::montgomery_mul`.

This function performs Montgomery multiplication.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes as input two UnpackedScalars m and m' that are assumed to be
      in Montgomery form. Then computes and returns an UnpackedScalar w
      (also in Montgomery form) that represents the Montgomery multiplication
      of m and m'.

    • Montgomery multiplication is defined as: MontMul(m, m') = (m * m' * R⁻¹) mod L
      where R = 2^260 is the Montgomery constant.

natural language specs:

    • For any two UnpackedScalars m and m' in Montgomery form:
      - (Scalar52_as_Nat m * Scalar52_as_Nat m') mod L = (Scalar52_as_Nat w * R) mod L
      - This is equivalent to: w represents (m * m' * R⁻¹) mod L
-/

/-- **Spec and proof concerning `scalar.Scalar52.montgomery_mul`**:
- No panic (always returns successfully)
- The result w satisfies the Montgomery multiplication property:
  (m * m') ≡ w * R (mod L), where R = 2^260 is the Montgomery constant
-/
@[progress]
theorem montgomery_mul_spec (m m' : Scalar52)
    (hm : ∀ i < 5, m[i]!.val < 2 ^ 62) (hm' : ∀ i < 5, m'[i]!.val < 2 ^ 62) :
    montgomery_mul m m' ⦃ w =>
      (Scalar52_as_Nat m * Scalar52_as_Nat m') ≡ (Scalar52_as_Nat w * R) [MOD L] ∧
      (∀ i < 5, w[i]!.val < 2 ^ 62) ⦄ := by
  sorry


end curve25519_dalek.backend.serial.u64.scalar.Scalar52
