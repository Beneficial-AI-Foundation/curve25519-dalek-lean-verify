/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MulInternal
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::scalar::Scalar52::montgomery_mul`

This function performs Montgomery multiplication.

Source: "curve25519-dalek/src/backend/serial/u64/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option exponentiation.threshold 262

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::scalar::Scalar52::montgomery_mul`**
• No panic (always returns successfully)
• The result w satisfies the Montgomery multiplication property:
  (m * m') ≡ w * R (mod L), where R = 2^260 is the Montgomery constant -/
@[step]
theorem montgomery_mul_spec (m m' : Scalar52)
    (hm : ∀ i < 5, m[i]!.val < 2 ^ 62) (hm' : ∀ i < 5, m'[i]!.val < 2 ^ 62)
    (h_value : Scalar52_as_Nat m * Scalar52_as_Nat m' < R * L) :
    montgomery_mul m m' ⦃ (w : Scalar52) =>
      (Scalar52_as_Nat m * Scalar52_as_Nat m') ≡ (Scalar52_as_Nat w * R) [MOD L] ∧
      (∀ i < 5, w[i]!.val < 2 ^ 52) ∧
      Scalar52_as_Nat w < L ⦄ := by
  unfold montgomery_mul
  step*
  refine ⟨?_, w_post2, w_post3⟩
  simpa [a1_post1, eq_comm] using w_post1

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
