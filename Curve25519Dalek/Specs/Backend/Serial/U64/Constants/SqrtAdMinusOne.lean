/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec Theorem for `constants::SQRT_AD_MINUS_ONE`

Specification and proof for the constant `SQRT_AD_MINUS_ONE`.

This constant represents sqrt(a*d - 1) where a and d are the twisted Edwards
curve parameters in the defining equation ax^2 + y^2 = 1 + dx^2y^2, with a = -1 (mod p).

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-
natural language description:

    • constants.SQRT_AD_MINUS_ONE is a constant representing one of the square roots of (a*d - 1) (mod p)
      where a and d are the parameters in the defining curve equation ax^2 + y^2 = 1 + dx^2y^2
      (for Curve25519 we have a = -1).
    • The field element constants.SQRT_AD_MINUS_ONE is represented as five u64 limbs (51-bit limbs)

natural language specs:

    • Field51_as_Nat(constants.SQRT_AD_MINUS_ONE)^2 ≡ (a*d - 1) (mod p).
-/

/-- The concrete field element returned by SQRT_AD_MINUS_ONE (extracted from the Result wrapper). -/
def SQRT_AD_MINUS_ONE_raw : backend.serial.u64.field.FieldElement51 :=
  Array.make 5#usize [2241493124984347#u64, 425987919032274#u64, 2207028919301688#u64,
    1220490630685848#u64, 974799131293748#u64]

/-- **Spec and proof concerning `backend.serial.u64.constants.SQRT_AD_MINUS_ONE`**:
- Field51_as_Nat(constants.SQRT_AD_MINUS_ONE) is a square root of (a*d - 1) modulo p, i.e.
  `(Field51_as_Nat constants.SQRT_AD_MINUS_ONE)^2 ≡ (a*d - 1) (mod p)`.
-/
@[step]
theorem SQRT_AD_MINUS_ONE_spec :
    SQRT_AD_MINUS_ONE ⦃ result =>
    (Field51_as_Nat result)^2 % p = (a * d - 1) % p ∧
    (∀ i < 5, result[i]!.val < 2^51) ∧
    result = SQRT_AD_MINUS_ONE_raw ⦄ := by
  unfold SQRT_AD_MINUS_ONE field.FieldElement51.from_limbs SQRT_AD_MINUS_ONE_raw
  simp only [spec_ok]
  exact ⟨by decide, fun i hi => by interval_cases i <;> decide, trivial⟩

end curve25519_dalek.backend.serial.u64.constants
