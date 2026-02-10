/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MulInternal_Hoare
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce_Hoare
import Curve25519Dalek.mvcgen
import Std.Do
import Std.Tactic.Do
open Std.Do
/-! # Spec Theorem for `Scalar52::montgomery_mul`

Specification and proof for `Scalar52::montgomery_mul`.

This function performs Montgomery multiplication.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

-/

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

@[spec]
theorem montgomery_mul_hoare_spec (m m' : Scalar52) (range_a : ∀ i, i < 5 → (m[i]!).val < 2 ^ 62)
    (range_b : ∀ i, i < 5 → (m'[i]!).val < 2 ^ 62) :
    ⦃⌜True⌝⦄
    montgomery_mul m m'
    ⦃⇓ w => ⌜(Scalar52_as_Nat m * Scalar52_as_Nat m') ≡ (Scalar52_as_Nat w * R) [MOD L]⌝⦄ := by
  mvcgen [montgomery_mul]
  intro h1
  rw [Nat.ModEq]
  grind

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
