/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::constants::SQRT_AD_MINUS_ONE`

This constant represents a square root of `a*d - 1 (mod p)`, where `a` and `d` are the
twisted Edwards curve parameters in the defining equation `a*x^2 + y^2 = 1 + d*x^2*y^2`
(with `a = -1` for Curve25519) and `p = 2^255 - 19`. It is encoded as a 5-limb 51-bit
`FieldElement51`.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- The concrete field element returned by SQRT_AD_MINUS_ONE (extracted from the Result wrapper). -/
def SQRT_AD_MINUS_ONE_raw : backend.serial.u64.field.FieldElement51 :=
  Array.make 5#usize [2241493124984347#u64, 425987919032274#u64, 2207028919301688#u64,
    1220490630685848#u64, 974799131293748#u64]

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::SQRT_AD_MINUS_ONE`**
• The function always succeeds (no panic)
• `(Field51_as_Nat SQRT_AD_MINUS_ONE)^2 ≡ a*d - 1 (mod p)`, i.e. it is a square root
• Every limb is bounded by `2 ^ 51`
• The result equals the concrete witness `SQRT_AD_MINUS_ONE_raw`
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
