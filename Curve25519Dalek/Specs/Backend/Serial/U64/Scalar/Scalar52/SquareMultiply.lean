/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomerySquare

/-! # Spec theorem for `curve25519_dalek::scalar::Scalar52::montgomery_invert::square_multiply`

This is a helper function for the addition chain in the inversion algorithm.
It performs repeated Montgomery squaring followed by a Montgomery multiplication.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek.backend.serial.u64.scalar
open curve25519_dalek.backend.serial.u64.scalar.Scalar52
namespace curve25519_dalek.scalar.Scalar52

/-- Spec theorem for
`curve25519_dalek::scalar::Scalar52::montgomery_invert::square_multiply_loop`
• No panic for canonical input `y` (limbs `< 2 ^ 52`, value `< L`) — self-maintaining since
  `montgomery_square` always produces canonical output
• After `k = squarings - i` Montgomery squarings: `res * R ^ (2^k - 1) ≡ y ^ (2^k) (mod L)`
• Every output limb is `< 2 ^ 52`
• The output value is canonical (`< L`) -/
theorem square_multiply_loop_spec (y : Scalar52) (squarings i : Usize) (hi : i.val ≤ squarings.val)
    (h_y_bound : ∀ j < 5, y[j]!.val < 2 ^ 52)
    (h_y_canonical : Scalar52_as_Nat y < L) :
    montgomery_invert.square_multiply_loop y squarings i ⦃ (res : Scalar52) =>
      (Scalar52_as_Nat res * R ^ (2 ^ (squarings.val - i.val) - 1)) % L =
        (Scalar52_as_Nat y) ^ (2 ^ (squarings.val - i.val)) % L ∧
      (∀ j < 5, res[j]!.val < 2 ^ 52) ∧
      Scalar52_as_Nat res < L ⦄ := by
  induction h_rem : (squarings.val - i.val) generalizing i y with
  | zero =>
    have : i = squarings := by
      have h_ge : squarings.val ≤ i.val := Nat.le_of_sub_eq_zero h_rem
      have h_val_eq : i.val = squarings.val := Nat.le_antisymm hi h_ge
      cases i; cases squarings;
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
        getElem!_pos, le_refl, tsub_self, UScalar.mk.injEq, UScalarTy.Usize_numBits_eq]
      exact BitVec.eq_of_toNat_eq h_val_eq
    unfold montgomery_invert.square_multiply_loop
    simp only [this, lt_self_iff_false, ↓reduceIte, pow_zero, tsub_self, mul_one, pow_one,
      Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, spec_ok, true_and]
    refine ⟨fun j hj => ?_, h_y_canonical⟩
    simpa using h_y_bound j hj
  | succ n ih =>
    unfold montgomery_invert.square_multiply_loop
    simp only [UScalar.lt_equiv, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]
    split
    · let* ⟨ y1, y1_post1, y1_post2, y1_post3 ⟩ ← montgomery_square_spec
      · -- y < L → y * y < L * L < R * L
        calc Scalar52_as_Nat y * Scalar52_as_Nat y
            < L * L := Nat.mul_lt_mul_of_lt_of_lt h_y_canonical h_y_canonical
          _ < R * L := Nat.mul_lt_mul_of_pos_right (by unfold R L; omega) (by unfold L; omega)
      let* ⟨ i1, i1_post ⟩ ← Usize.add_spec
      let* ⟨ res, res_post1, res_post2, res_post3 ⟩ ← ih
      refine ⟨ ?_, ?_, res_post3 ⟩
      · have h_pow_split : 2 ^ (n + 1) - 1 = (2 ^ n - 1) + 2 ^ n := by
          have : 1 ≤ 2^n := Nat.one_le_pow n 2 (by decide)
          omega
        rw [h_pow_split, Nat.pow_add]
        ring_nf at ⊢ res_post1
        rw [Nat.mul_mod, res_post1, ← Nat.mul_mod, ← Nat.mul_pow, Nat.pow_mod, ← y1_post1,
          ← Nat.pow_mod]
        ring_nf
      intro j hj; simpa using res_post2 j hj
    · have : squarings.val - i.val = n + 1 := by assumption
      agrind


/-- **Spec theorem for `curve25519_dalek::scalar::Scalar52::montgomery_invert::square_multiply`**
• Preconditions: Inputs `y` and `x` are canonical (limbs < 2^52, value < L).
• Postcondition:
  The result `res` satisfies: res * R^(2^squarings) = y^(2^squarings) * x (mod L)
  and is canonical. -/
@[step]
theorem square_multiply_spec (y : Scalar52) (squarings : Usize) (x : Scalar52)
    (hy : ∀ i < 5, y[i]!.val < 2 ^ 52) (hx : ∀ i < 5, x[i]!.val < 2 ^ 52)
    (h_y_canonical : Scalar52_as_Nat y < L)
    (h_x_canonical : Scalar52_as_Nat x < L) :
    montgomery_invert.square_multiply y squarings x ⦃ (res : Scalar52) =>
      (Scalar52_as_Nat res * R ^ (2 ^ squarings.val)) % L =
        ((Scalar52_as_Nat y) ^ (2 ^ squarings.val) * (Scalar52_as_Nat x)) % L ∧
      (∀ i < 5, res[i]!.val < 2 ^ 52) ∧
      Scalar52_as_Nat res < L ⦄ := by
  unfold montgomery_invert.square_multiply
  let* ⟨ loop_res, h_loop_math, h_loop_bound, h_loop_canonical ⟩ ← square_multiply_loop_spec
  simp only [tsub_zero] at h_loop_math
  let* ⟨ mul_res, h_mul_math, h_mul_bound, h_mul_canonical ⟩ ← montgomery_mul_spec
  · -- loop_res < L, x < L → loop_res * x < L * L < R * L
    calc Scalar52_as_Nat loop_res * Scalar52_as_Nat x
        < L * L := Nat.mul_lt_mul_of_lt_of_lt h_loop_canonical h_x_canonical
      _ < R * L := Nat.mul_lt_mul_of_pos_right (by unfold R L; omega) (by unfold L; omega)
  refine ⟨?_, h_mul_bound, h_mul_canonical⟩
  have h_pow_split : R ^ (2 ^ squarings.val) = R * R ^ (2 ^ squarings.val - 1) := by
    rw [← Nat.pow_succ']; congr 1
    have : 1 ≤ 2 ^ squarings.val := Nat.one_le_pow _ _ (by decide)
    omega
  have h_mul_eq : (Scalar52_as_Nat mul_res * R) % L =
                  (Scalar52_as_Nat loop_res * Scalar52_as_Nat x) % L :=
    h_mul_math.symm
  rw [h_pow_split, ← Nat.mul_assoc, Nat.mul_mod, h_mul_eq, ← Nat.mul_mod]
  ring_nf
  rw [Nat.mul_comm (Scalar52_as_Nat loop_res), Nat.mul_assoc, Nat.mul_mod, h_loop_math]
  rw [← Nat.mul_mod]


end curve25519_dalek.scalar.Scalar52
