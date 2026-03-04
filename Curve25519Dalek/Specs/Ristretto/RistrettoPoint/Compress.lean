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

open Aeneas Aeneas.Std Result Aeneas.Std.WP Edwards
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.math curve25519_dalek.ristretto
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
  -- Shared bridge: lift conditional_assign s1 to Field51_as_Nat level
  · have h_s1_nat : Field51_as_Nat s1 =
        if s_is_negative.val = 1#u8 then Field51_as_Nat s_neg else Field51_as_Nat s := by
      unfold Field51_as_Nat
      split <;> rename_i hc
      · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
        have := s1_post i hi; rw [if_pos hc] at this
        exact congrArg (fun u => 2 ^ (51 * i) * u.val) this
      · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
        have := s1_post i hi; rw [if_neg hc] at this
        exact congrArg (fun u => 2 ^ (51 * i) * u.val) this
    -- Shared bridge: U8x32_as_Nat a = Field51_as_Nat s1 % p
    have h_a_eq : U8x32_as_Nat a = Field51_as_Nat s1 % p := by
      have h_mod := a_post_1
      rw [Nat.ModEq] at h_mod
      rw [Nat.mod_eq_of_lt a_post_2] at h_mod
      exact h_mod
    -- Shared bridge: parity of s1 mod p is 0
    have h_s1_parity : Field51_as_Nat s1 % p % 2 = 0 := by
      rw [h_s1_nat]
      split <;> rename_i hc
      · -- s_is_negative = 1: s1 = s_neg, need (Field51_as_Nat s_neg % p) % 2 = 0
        have h_s_odd := s_is_negative_post.mp hc
        have h_sum := s_neg_post_1
        -- Field51_as_Nat s_neg ≡ -(Field51_as_Nat s) [MOD p]
        have h_s_mod_ne : Field51_as_Nat s % p ≠ 0 := by
          intro h_zero; rw [h_zero] at h_s_odd; simp at h_s_odd
        have h_s_mod_lt : Field51_as_Nat s % p < p := Nat.mod_lt _ (by decide)
        have h_s_mod_pos : 0 < Field51_as_Nat s % p := Nat.pos_of_ne_zero h_s_mod_ne
        have h_neg_mod : Field51_as_Nat s_neg % p = p - Field51_as_Nat s % p := by
          have h1 : (Field51_as_Nat s % p + Field51_as_Nat s_neg % p) % p = 0 := by
            rwa [Nat.add_mod] at h_sum
          have h2 : Field51_as_Nat s_neg % p < p := Nat.mod_lt _ (by decide)
          have h_dvd := Nat.dvd_of_mod_eq_zero h1
          have h_sum_pos : 0 < Field51_as_Nat s % p + Field51_as_Nat s_neg % p := by omega
          have h_le := Nat.le_of_dvd h_sum_pos h_dvd
          have h_sub_dvd : p ∣ (Field51_as_Nat s % p + Field51_as_Nat s_neg % p - p) :=
            Nat.dvd_sub h_dvd (dvd_refl p)
          rcases Nat.eq_zero_or_pos (Field51_as_Nat s % p + Field51_as_Nat s_neg % p - p) with h | h
          · omega
          · exact absurd (Nat.le_of_dvd h h_sub_dvd) (by omega)
        rw [h_neg_mod]
        have hp_odd : p % 2 = 1 := by decide
        omega
      · -- s_is_negative ≠ 1: s1 = s, which has even parity
        have h_s_even : Field51_as_Nat s % p % 2 ≠ 1 := by
          intro h_odd; exact hc (s_is_negative_post.mpr h_odd)
        omega
    -- Shared bridge: parity of U8x32_as_Nat a
    have h_a_parity : U8x32_as_Nat a % 2 = 0 := by
      rw [h_a_eq]; exact h_s1_parity
    refine ⟨?_, ?_⟩
    · -- Goal 36: IsValid (decompress_pure succeeds)
      unfold CompressedRistretto.IsValid
      sorry
    · -- Goal 37: compress_pure matches byte output
      -- Key bridge: s1.toField = compress_s self.toPoint
      -- Key bridge: s1.toField = compress_s self.toPoint
      have h_key : s1.toField = compress_s self.toPoint := by
        -- Setup: affine coordinates and IsValid properties
        set P := self.toPoint with hP_def
        have hvalid := h.1
        have ⟨hpx, hpy⟩ := edwards.EdwardsPoint.toPoint_of_isValid hvalid
        have hZ_ne := hvalid.Z_ne_zero  -- Z.toField ≠ 0
        have hT_rel := hvalid.T_relation  -- X.toField * Y.toField = T.toField * Z.toField
        -- Step 1: s1.toField = abs_edwards(s.toField) via conditional negation
        have h_s_neg_field : s_neg.toField = -s.toField := by
          unfold FieldElement51.toField
          have := lift_mod_eq _ _
            (show (Field51_as_Nat s + Field51_as_Nat s_neg) % p = 0 % p by
              rw [Nat.zero_mod]; exact s_neg_post_1)
          push_cast at this; linear_combination this
        have h_s1_select : s1.toField =
            if s_is_negative.val = 1#u8 then s_neg.toField else s.toField := by
          unfold FieldElement51.toField; rw [h_s1_nat]; split <;> rfl
        have h_s1_abs : s1.toField = abs_edwards s.toField := by
          rw [h_s1_select, h_s_neg_field, abs_edwards, is_negative]
          by_cases hc : s_is_negative.val = 1#u8
          · rw [if_pos hc]
            have : (s.toField.val % 2 == 1) = true := by
              rw [beq_iff_eq]; unfold FieldElement51.toField;
              rw [ZMod.val_natCast]
              exact s_is_negative_post.mp hc
            simp only [this, ite_true]
          · rw [if_neg hc]
            have : (s.toField.val % 2 == 1) = false := by
              rw [Bool.eq_false_iff]; intro hh; rw [beq_iff_eq] at hh
              exact hc (s_is_negative_post.mpr
                (by unfold FieldElement51.toField at hh; rwa [ZMod.val_natCast] at hh))
            simp only [this, Bool.false_eq_true, ↓reduceIte]
        -- Step 2: s.toField ^ 2 = (compress_den_inv P * (1 - compress_y_final P)) ^ 2
        -- Note: We do NOT need SQRT_M1.toField = sqrt_m1 or INVSQRT_A_MINUS_D.toField = invsqrt_a_minus_d.
        -- The sign ambiguity (±) of SQRT_M1.toField is compensated by the y_sign flag,
        -- and we only need INVSQRT_A_MINUS_D.toField² = invsqrt_a_minus_d² (from both being inv sqrt of a-d).
        -- Mul bridges (lift Nat mod postconditions to ZMod p)
        have hb_u1 : u1.toField = z_plus_y.toField * z_minus_y.toField := by
          unfold FieldElement51.toField; have := lift_mod_eq _ _ u1_post_1
          push_cast at this; exact this
        have hb_u2 : u2.toField = self.X.toField * self.Y.toField := by
          unfold FieldElement51.toField; have := lift_mod_eq _ _ u2_post_1
          push_cast at this; exact this
        have hb_u2_sq : u2_sq.toField = u2.toField ^ 2 := by
          unfold FieldElement51.toField; have := lift_mod_eq _ _ u2_sq_post_1
          push_cast at this; exact this
        have hb_u1_u2_sq : u1_u2_sq.toField = u1.toField * u2_sq.toField := by
          unfold FieldElement51.toField; have := lift_mod_eq _ _ u1_u2_sq_post_1
          push_cast at this; exact this
        have hb_i1 : i1.toField = __discr.2.toField * u1.toField := by
          unfold FieldElement51.toField; have := lift_mod_eq _ _ i1_post_1
          push_cast at this; exact this
        have hb_i2 : i2.toField = __discr.2.toField * u2.toField := by
          unfold FieldElement51.toField; have := lift_mod_eq _ _ i2_post_1
          push_cast at this; exact this
        have hb_i2_T : i2_T.toField = i2.toField * self.T.toField := by
          unfold FieldElement51.toField; have := lift_mod_eq _ _ i2_T_post_1
          push_cast at this; exact this
        have hb_z_inv : z_inv.toField = i1.toField * i2_T.toField := by
          unfold FieldElement51.toField; have := lift_mod_eq _ _ z_inv_post_1
          push_cast at this; exact this
        have hb_iX : iX.toField = self.X.toField *
            backend.serial.u64.constants.SQRT_M1.toField := by
          unfold FieldElement51.toField; have := lift_mod_eq _ _ iX_post_1
          push_cast at this; exact this
        have hb_iY : iY.toField = self.Y.toField *
            backend.serial.u64.constants.SQRT_M1.toField := by
          unfold FieldElement51.toField; have := lift_mod_eq _ _ iY_post_1
          push_cast at this; exact this
        have hb_enchanted : enchanted_denominator.toField = i1.toField *
            backend.serial.u64.constants.INVSQRT_A_MINUS_D.toField := by
          unfold FieldElement51.toField; have := lift_mod_eq _ _ enchanted_denominator_post_1
          push_cast at this; exact this
        have hb_t_z_inv : t_z_inv.toField = self.T.toField * z_inv.toField := by
          unfold FieldElement51.toField; have := lift_mod_eq _ _ t_z_inv_post_1
          push_cast at this; exact this
        have hb_x_z_inv : x_z_inv.toField = X.toField * z_inv.toField := by
          unfold FieldElement51.toField; have := lift_mod_eq _ _ x_z_inv_post_1
          push_cast at this; exact this
        have hb_s : s.toField = i21.toField * z_minus_y2.toField := by
          unfold FieldElement51.toField; have := lift_mod_eq _ _ s_post_1
          push_cast at this; exact this
        -- Sub bridges
        have hb_zmy : z_minus_y.toField = self.Z.toField - self.Y.toField := by
          unfold FieldElement51.toField
          have := lift_mod_eq _ _ z_minus_y_post_2
          push_cast at this; linear_combination this
        have hb_zmy2 : z_minus_y2.toField = self.Z.toField - Y1.toField := by
          unfold FieldElement51.toField
          have := lift_mod_eq _ _ z_minus_y2_post_2
          push_cast at this; linear_combination this
        -- Add bridge
        have hb_zpy : z_plus_y.toField = self.Z.toField + self.Y.toField := by
          unfold FieldElement51.toField Field51_as_Nat
          have h : ∑ i ∈ Finset.range 5, 2 ^ (51 * i) * z_plus_y[i]!.val =
              ∑ i ∈ Finset.range 5, 2 ^ (51 * i) * self.Z[i]!.val +
              ∑ i ∈ Finset.range 5, 2 ^ (51 * i) * self.Y[i]!.val := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i hi; rw [Finset.mem_range] at hi
            rw [z_plus_y_post_1 i hi]; ring
          exact (congrArg Nat.cast h).trans (Nat.cast_add _ _)
        -- Neg bridge
        have hb_y_neg : y_neg.toField = -Y.toField := by
          unfold FieldElement51.toField
          have := lift_mod_eq _ _
            (show (Field51_as_Nat Y + Field51_as_Nat y_neg) % p = 0 % p by
              rw [Nat.zero_mod]; exact y_neg_post_1)
          push_cast at this; linear_combination this
        -- Conditional assign bridges (lift limb-level ite to toField-level ite)
        have hb_i21_nat : Field51_as_Nat i21 =
            if rotate.val = 1#u8 then Field51_as_Nat enchanted_denominator
            else Field51_as_Nat i2 := by
          unfold Field51_as_Nat; split <;> rename_i hc
          · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
            have := i21_post i hi; rw [if_pos hc] at this
            exact congrArg (fun u => 2 ^ (51 * i) * u.val) this
          · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
            have := i21_post i hi; rw [if_neg hc] at this
            exact congrArg (fun u => 2 ^ (51 * i) * u.val) this
        have hb_i21 : i21.toField =
            if rotate.val = 1#u8 then enchanted_denominator.toField else i2.toField := by
          unfold FieldElement51.toField; rw [hb_i21_nat]; split <;> rfl
        have hb_Y_nat : Field51_as_Nat Y =
            if rotate.val = 1#u8 then Field51_as_Nat iX else Field51_as_Nat self.Y := by
          unfold Field51_as_Nat; split <;> rename_i hc
          · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
            have := Y_post i hi; rw [if_pos hc] at this
            exact congrArg (fun u => 2 ^ (51 * i) * u.val) this
          · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
            have := Y_post i hi; rw [if_neg hc] at this
            exact congrArg (fun u => 2 ^ (51 * i) * u.val) this
        have hb_Y : Y.toField =
            if rotate.val = 1#u8 then iX.toField else self.Y.toField := by
          unfold FieldElement51.toField; rw [hb_Y_nat]; split <;> rfl
        have hb_X_nat : Field51_as_Nat X =
            if rotate.val = 1#u8 then Field51_as_Nat iY else Field51_as_Nat self.X := by
          unfold Field51_as_Nat; split <;> rename_i hc
          · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
            have := X_post i hi; rw [if_pos hc] at this
            exact congrArg (fun u => 2 ^ (51 * i) * u.val) this
          · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
            have := X_post i hi; rw [if_neg hc] at this
            exact congrArg (fun u => 2 ^ (51 * i) * u.val) this
        have hb_X : X.toField =
            if rotate.val = 1#u8 then iY.toField else self.X.toField := by
          unfold FieldElement51.toField; rw [hb_X_nat]; split <;> rfl
        have hb_Y1_nat : Field51_as_Nat Y1 =
            if y_sign.val = 1#u8 then Field51_as_Nat y_neg else Field51_as_Nat Y := by
          unfold Field51_as_Nat; split <;> rename_i hc
          · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
            have := Y1_post i hi; rw [if_pos hc] at this
            exact congrArg (fun u => 2 ^ (51 * i) * u.val) this
          · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
            have := Y1_post i hi; rw [if_neg hc] at this
            exact congrArg (fun u => 2 ^ (51 * i) * u.val) this
        have hb_Y1 : Y1.toField =
            if y_sign.val = 1#u8 then y_neg.toField else Y.toField := by
          unfold FieldElement51.toField; rw [hb_Y1_nat]; split <;> rfl
        -- ═══ Projective coordinate relations ═══
        have h_u1_proj : u1.toField = self.Z.toField ^ 2 - self.Y.toField ^ 2 := by
          rw [hb_u1, hb_zpy, hb_zmy]; ring
        have h_u1_u2_sq_val : u1_u2_sq.toField =
            (self.Z.toField ^ 2 - self.Y.toField ^ 2) *
            (self.X.toField * self.Y.toField) ^ 2 := by
          rw [hb_u1_u2_sq, hb_u2_sq, h_u1_proj, hb_u2];
        -- ═══ QR argument (IsSquare from self.IsValid) ═══
        -- u1_u2_sq.toField = Z⁶ · (compress_u1 P · compress_u2 P²) via projective→affine
        -- For valid Ristretto points, IsSquare(Z²-Y²) → IsSquare(compress_u1 P)
        -- And compress_u2 P² is always a square → product is a square
        -- In QR case: I² · u1_u2_sq = 1
        have h_I_sq_mul : u1_u2_sq.toField ≠ 0 →
            __discr.2.toField ^ 2 * u1_u2_sq.toField = 1 := by
          intro h_ne
          have h_ne_nat : Field51_as_Nat u1_u2_sq % p ≠ 0 := by
            rwa [FieldElement51.toField, ne_eq, ZMod.natCast_eq_zero_iff,
                 Nat.dvd_iff_mod_eq_zero] at h_ne
          have h_qr : ∃ x, x ^ 2 * (Field51_as_Nat u1_u2_sq % p) % p = 1 := by sorry
          have h_post := (__discr_post_4 ⟨h_ne_nat, h_qr⟩).2
          -- Lift Nat % p equation to Nat.ModEq, then to ZMod
          have hmm : ∀ a, (a % p) ≡ a [MOD p] := fun a => by
            change (a % p) % p = a % p
            exact Nat.mod_eq_of_lt (Nat.mod_lt a (by decide))
          have h1 : (Field51_as_Nat __discr.2 % p) ^ 2 *
              (Field51_as_Nat u1_u2_sq % p) ≡ 1 [MOD p] := by
            change _ % _ = _ % _
            rw [h_post, Nat.mod_eq_of_lt (by decide : 1 < p)]
          have h_modeq : Field51_as_Nat __discr.2 ^ 2 *
              Field51_as_Nat u1_u2_sq ≡ 1 [MOD p] :=
            ((hmm _).symm.pow 2).mul (hmm _).symm |>.trans h1
          unfold FieldElement51.toField
          have := lift_mod_eq _ _ h_modeq; push_cast at this; exact this
        -- ═══ z_inv.toField = 1/Z (key identity from QR) ═══
        have h_z_inv_chain : z_inv.toField =
            __discr.2.toField ^ 2 * u1.toField * u2.toField *
            self.T.toField := by
          rw [hb_z_inv, hb_i1, hb_i2_T, hb_i2]; ring
        -- ═══ Step 2: The squared equality ═══
        have h_sq_eq : s.toField ^ 2 =
            (compress_den_inv P * (1 - compress_y_final P)) ^ 2 := by
          sorry
        -- Conclude
        rw [h_s1_abs]; unfold compress_s
        exact abs_edwards_eq_of_sq_eq h_sq_eq
      -- compress_pure P = (compress_s P).val = s1.toField.val = Field51_as_Nat s1 % p
      change compress_pure self.toPoint = U8x32_as_Nat a
      unfold compress_pure
      rw [← h_key, FieldElement51.toField, ZMod.val_natCast]
      exact h_a_eq.symm

end curve25519_dalek.ristretto.RistrettoPoint
