/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.SquareInternal
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MulInternal
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.RR

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::scalar::Scalar52::square`

This function performs regular scalar squaring (not Montgomery squaring).

Source: "curve25519-dalek/src/backend/serial/u64/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option exponentiation.threshold 262

/- Helper lemmas/theorems -/

-- Helper theorem to cancel R [mod L] on right (same as in Mul.lean)
private theorem cancelR {a b : ℕ} (h : a * R ≡ b * R [MOD L]) : a ≡ b [MOD L] := by
  have hcoprime : Nat.Coprime R L := by
    unfold R L Nat.Coprime
    simp
  have h1 := Nat.Coprime.symm hcoprime
  exact Nat.ModEq.cancel_right_of_coprime h1 h

/- End of helper lemmas/theorems -/

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::scalar::Scalar52::square`**
• No panic (always returns successfully)
• The result represents the square of the input scalar modulo L
• Input scalar should have limbs bounded by 2^62 (standard Scalar52 representation)
• Output limbs are bounded by 2^52
• `h_value`: Required by `montgomery_reduce` (see `MontgomeryReduce.lean`). The second
  reduce is auto-satisfied since `aa < L` and `RR < L` give `aa*RR < L² < R*L`. -/
@[step]
theorem square_spec (self : Scalar52)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 62)
    (h_value : Scalar52_as_Nat self * Scalar52_as_Nat self < R * L) :
    square self ⦃ (result : Scalar52) =>
      Scalar52_as_Nat result ≡ Scalar52_as_Nat self * Scalar52_as_Nat self [MOD L] ∧
      Scalar52_as_Nat result < L ∧
      ∀ i < 5, result[i]!.val < 2 ^ 52 ⦄ := by
  unfold square
  let* ⟨ a, a_post1, a_post2 ⟩ ← square_internal_spec
  let* ⟨ aa, aa_post1, aa_post2, aa_post3 ⟩ ← montgomery_reduce_spec
  let* ⟨ a1, a1_post1, a1_post2 ⟩ ← mul_internal_spec
  · unfold constants.RR; decide
  let* ⟨ result, result_post1, result_post2, result_post3 ⟩ ← montgomery_reduce_spec
  · -- aa < L (from montgomery_reduce), RR < L (concrete constant), so aa * RR < L * L < R * L
    rw [a1_post1]
    have h_RR_lt : Scalar52_as_Nat constants.RR < L := by
      unfold constants.RR Scalar52_as_Nat L; decide
    calc Scalar52_as_Nat aa * Scalar52_as_Nat constants.RR
        < L * L := Nat.mul_lt_mul_of_lt_of_lt aa_post3 h_RR_lt
      _ < R * L := Nat.mul_lt_mul_of_pos_right (by unfold R L; omega) (by unfold L; omega)
  refine ⟨?_, result_post3, result_post2⟩
  have h_result_R_aa_RR : Scalar52_as_Nat result * R ≡
    Scalar52_as_Nat aa * Scalar52_as_Nat constants.RR [MOD L] := by
      rw [a1_post1] at result_post1
      rw [Nat.ModEq]
      exact result_post1
  have h_result_R_aa_R_R : Scalar52_as_Nat result * R ≡ Scalar52_as_Nat aa * R * R [MOD L] := by
    have := curve25519_dalek.backend.serial.u64.constants.RR_spec
    grind only [Nat.ModEq, Nat.mul_mod, Nat.pow_two, Nat.mul_assoc]
  have h_result_R_a_R : Scalar52_as_Nat result * R ≡ Scalar52_wide_as_Nat a * R [MOD L] := by
    rw [← Nat.ModEq] at aa_post1
    exact Nat.ModEq.trans h_result_R_aa_R_R (Nat.ModEq.mul_right R aa_post1)
  have h_result_R_self_sq_R : Scalar52_as_Nat result * R ≡
    Scalar52_as_Nat self * Scalar52_as_Nat self * R [MOD L] := by
      rw [a_post1] at h_result_R_a_R
      exact h_result_R_a_R
  grind only [cancelR]

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
