/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MulInternal
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce
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
theorem montgomery_reduce_spec' (a : Array U128 9#usize) :
⦃⌜True⌝⦄
montgomery_reduce a
⦃⇓ m => ⌜montgomery_reduce a = ok m ∧
    (Scalar52_as_Nat m * R) % L = Scalar52_wide_as_Nat a % L⌝⦄
  := by
  sorry

@[spec]
theorem mul_internal_spec' (a b : Array U64 5#usize)
(ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62)
(hb : ∀ i, i < 5 → (b[i]!).val < 2 ^ 62) :
⦃⌜True⌝⦄
mul_internal a b
⦃⇓ result => ⌜mul_internal a b = ok result ∧
  Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat b⌝⦄
  := by
  sorry


@[spec]
theorem montgomery_mul_spec' (m m' : Scalar52)
(range_a : ∀ i, i < 5 → (m[i]!).val < 2 ^ 62)
(range_b : ∀ i, i < 5 → (m'[i]!).val < 2 ^ 62)
 :
⦃⌜True⌝⦄
montgomery_mul m m'
⦃⇓ w => ⌜montgomery_mul m m' = ok w ∧
    (Scalar52_as_Nat m * Scalar52_as_Nat m') ≡ (Scalar52_as_Nat w * R) [MOD L]⌝⦄
  := by
  -- unfold montgomery_mul
  mvcgen [montgomery_mul]
  grind
  sorry
  sorry
end curve25519_dalek.backend.serial.u64.scalar.Scalar52
