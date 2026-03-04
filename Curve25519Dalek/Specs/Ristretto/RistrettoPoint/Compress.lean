/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Field.FieldElement51.InvSqrt
import Curve25519Dalek.Specs.Field.FieldElement51.IsNegative
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.SQRT_M1
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.INVSQRT_A_MINUS_D

/-! # Spec Theorem for `RistrettoPoint::compress`

Specification and proof for `RistrettoPoint::compress`.

This function implements the Ristretto compression (ENCODE) function, which maps a
RistrettoPoint to its canonical 32-byte representation. The function is defined in the

- [Ristretto specification](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-08#section-4.3.2).

It takes a RistrettoPoint (which represents an equivalence class of Edwards points) and produces a unique, canonical byte representation.
>>
**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.ristretto.RistrettoPoint

/-
natural language description:

• Takes a RistrettoPoint (represented internally as an even EdwardsPoint in extended coordinates
  (X, Y, Z, T)) and compresses it to a canonical 32-byte representation according to the
  Ristretto ENCODE function specified in:

  https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-08#section-4.3.2

  Arithmetics are performed in the field 𝔽ₚ where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic) for all valid RistrettoPoint inputs
• The output is a valid CompressedRistretto 32-byte representation
• The output accurately reflects the output of the pure mathematical compression function
-/

-- maxHeartbeats increased: compress has many sub-calls, progress* needs more time after Aeneas update
set_option maxHeartbeats 1600000 in
/-- **Spec and proof concerning `ristretto.RistrettoPoint.compress`**:
• The function always succeeds (no panic) for all valid RistrettoPoint inputs
• The output is a valid CompressedRistretto 32-byte representation
• The output accurately reflects the output of the pure mathematical compression function
-/
@[progress]
theorem compress_spec (self : RistrettoPoint) (h : self.IsValid) :
    compress self ⦃ (result : CompressedRistretto) =>
      result.IsValid ∧
      math.compress_pure self.toPoint = U8x32_as_Nat result ⦄ := by
  unfold compress
  progress*

  -- Goal 1: Z limbs < 2^53 (from IsValid)
  · intro i hi; exact h.1.Z_bounds i hi
  -- Goal 2: Y limbs < 2^53 (from IsValid)
  · intro i hi; exact h.1.Y_bounds i hi
  -- Goal 3: Z limbs < 2^63 (sub precond)
  · intro i hi; have := h.1.Z_bounds i hi; omega
  -- Goal 4: Y limbs < 2^54 (sub precond)
  · intro i hi; have := h.1.Y_bounds i hi; omega
  -- Goal 5: z_minus_y < 2^54 (mul rhs precond)
  · intro i hi; have := z_minus_y_post_1 i hi; omega
  -- Goal 6: X limbs < 2^54 (mul lhs precond)
  · intro i hi; have := h.1.X_bounds i hi; omega
  -- Goal 7: Y limbs < 2^54 (mul rhs precond)
  · intro i hi; have := h.1.Y_bounds i hi; omega
  -- Goal 8: u2 limbs < 2^54 (square precond)
  · intro i hi; have := u2_post_2 i hi; omega
  -- Goal 9: u1 limbs < 2^54 (mul lhs precond)
  · intro i hi; have := u1_post_2 i hi; omega
  -- Goal 10: u2_sq limbs < 2^54 (mul rhs precond)
  · intro i hi; have := u2_sq_post_2 i hi; omega
  -- Goal 11: u1_u2_sq limbs ≤ 2^52 - 1 (invsqrt precond)
  · intro i hi; have := u1_u2_sq_post_2 i hi; omega
  -- Goal 12: invsqrt limbs < 2^54 (mul lhs precond)
  · intro i hi; have := __discr_post_1 i hi; omega
  -- Goal 13: u1 limbs < 2^54 (mul rhs precond, for i1)
  · intro i hi; have := u1_post_2 i hi; omega
  -- Goal 14: invsqrt limbs < 2^54 (mul lhs, for i2)
  · intro i hi; have := __discr_post_1 i hi; omega
  -- Goal 15: u2 limbs < 2^54 (mul rhs, for i2)
  · intro i hi; have := u2_post_2 i hi; omega
  -- Goal 16: i2 limbs < 2^54 (mul lhs, for i2_T)
  · intro i hi; have := i2_post_2 i hi; omega
  -- Goal 17: T limbs < 2^54 (mul rhs, for i2_T)
  · intro i hi; have := h.1.T_bounds i hi; omega
  -- Goal 18: i1 limbs < 2^54 (mul lhs, for z_inv)
  · intro i hi; have := i1_post_2 i hi; omega
  -- Goal 19: i2_T limbs < 2^54 (mul rhs, for z_inv)
  · intro i hi; have := i2_T_post_2 i hi; omega
  -- Goal 20: X limbs < 2^54 (mul lhs, for iX)
  · intro i hi; have := h.1.X_bounds i hi; omega
  -- Goal 21: SQRT_M1 limbs < 2^54 (mul rhs, for iX)
  · unfold backend.serial.u64.constants.SQRT_M1
    decide
  -- Goal 22: Y limbs < 2^54 (mul lhs, for iY)
  · intro i hi; have := h.1.Y_bounds i hi; omega
  -- Goal 23: SQRT_M1 limbs < 2^54 (mul rhs, for iY)
  · unfold backend.serial.u64.constants.SQRT_M1
    decide
  -- Goal 24: i1 limbs < 2^54 (mul lhs, for enchanted)
  · intro i hi; have := i1_post_2 i hi; omega
  -- Goal 25: INVSQRT_A_MINUS_D limbs < 2^54 (mul rhs, for enchanted)
  · unfold backend.serial.u64.constants.INVSQRT_A_MINUS_D
    decide
  -- Goal 26: T limbs < 2^54 (mul lhs, for t_z_inv)
  · intro i hi; have := h.1.T_bounds i hi; omega
  -- Goal 27: z_inv limbs < 2^54 (mul rhs, for t_z_inv)
  · intro i hi; have := z_inv_post_2 i hi; omega
  -- Goal 28: X (after cond_assign) limbs < 2^54 (mul lhs, for x_z_inv)
  · intro i hi
    simp only [X_post i hi]
    split_ifs
    · have := iY_post_2 i hi; omega
    · have := h.1.X_bounds i hi; omega
  -- Goal 29: z_inv limbs < 2^54 (mul rhs, for x_z_inv)
  · intro i hi; have := z_inv_post_2 i hi; omega
  -- Goal 30: Y (after cond_assign) limbs < 2^54 (neg precond)
  · intro i hi
    simp only [Y_post i hi]
    split_ifs
    · have := iX_post_2 i hi; omega
    · have := h.1.Y_bounds i hi; omega
  -- Goal 31: Z limbs < 2^63 (sub precond, for z_minus_y2)
  · intro i hi; have := h.1.Z_bounds i hi; omega
  -- Goal 32: Y1 (after cond_assign) limbs < 2^54 (sub precond)
  · intro i hi
    simp only [Y1_post i hi]
    split_ifs
    · have := y_neg_post_2 i hi; omega
    · simp only [Y_post i hi]
      split_ifs
      · have := iX_post_2 i hi; omega
      · have := h.1.Y_bounds i hi; omega
  -- Goal 33: i21 (after cond_assign) limbs < 2^54 (mul lhs, for s)
  · intro i hi
    simp only [i21_post i hi]
    split_ifs
    · have := enchanted_denominator_post_2 i hi; omega
    · have := i2_post_2 i hi; omega
  -- Goal 34: z_minus_y2 limbs < 2^54 (mul rhs, for s)
  · intro i hi; have := z_minus_y2_post_1 i hi; omega
  -- Goal 35: s limbs < 2^54 (neg precond for s_neg)
  · intro i hi; have := s_post_2 i hi; omega
  -- Goal 36: IsValid (decompress_pure succeeds)
  · constructor
    · unfold CompressedRistretto.IsValid
      sorry
  -- Goal 37: compress_pure matches byte output
    · sorry

end curve25519_dalek.ristretto.RistrettoPoint
