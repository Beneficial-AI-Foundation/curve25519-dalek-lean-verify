/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::constants::SQRT_M1`

This constant represents one of the square roots of `-1 (mod p)`, where `p = 2^255 - 19`.
It is encoded as a 5-limb 51-bit `FieldElement51`.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- The concrete field element returned by SQRT_M1 (extracted from the Result wrapper). -/
def SQRT_M1_raw : backend.serial.u64.field.FieldElement51 :=
  Array.make 5#usize [1718705420411056#u64, 234908883556509#u64, 2233514472574048#u64,
    2117202627021982#u64, 765476049583133#u64]

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::SQRT_M1`**
• The function always succeeds (no panic)
• The result equals the concrete witness `SQRT_M1_raw`
• `(Field51_as_Nat SQRT_M1)^2 ≡ -1 (mod p)`, i.e. it is a square root of `-1` modulo `p`
• Every limb is bounded by `2 ^ 51`
-/
@[step]
theorem SQRT_M1_spec :
    SQRT_M1 ⦃ result =>
    result = SQRT_M1_raw ∧
    (Field51_as_Nat result)^2 % p = p - 1 ∧
    (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  unfold SQRT_M1 field.FieldElement51.from_limbs SQRT_M1_raw
  simp only [spec_ok]
  exact ⟨trivial, by decide, fun i hi => by interval_cases i <;> decide⟩

end curve25519_dalek.backend.serial.u64.constants
