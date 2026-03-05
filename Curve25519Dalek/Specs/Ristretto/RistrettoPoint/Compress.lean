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


-- Bridge helpers: lift Field51_as_Nat postconditions to FieldElement51.toField equalities
private lemma bridge_mul {a b c : FieldElement51}
    (h : Field51_as_Nat a ≡ Field51_as_Nat b * Field51_as_Nat c [MOD p]) :
    a.toField = b.toField * c.toField := by
  unfold FieldElement51.toField; have := lift_mod_eq _ _ h; push_cast at this; exact this

private lemma bridge_sq {a b : FieldElement51}
    (h : Field51_as_Nat a ≡ Field51_as_Nat b ^ 2 [MOD p]) :
    a.toField = b.toField ^ 2 := by
  unfold FieldElement51.toField; have := lift_mod_eq _ _ h; push_cast at this; exact this

private lemma bridge_sub {a b c : FieldElement51}
    (h : (Field51_as_Nat a + Field51_as_Nat c) % p = Field51_as_Nat b % p) :
    a.toField = b.toField - c.toField := by
  unfold FieldElement51.toField; have := lift_mod_eq _ _ h
  push_cast at this; linear_combination this

private lemma bridge_neg {a b : FieldElement51}
    (h : Field51_as_Nat a + Field51_as_Nat b ≡ 0 [MOD p]) :
    b.toField = -a.toField := by
  unfold FieldElement51.toField; have := lift_mod_eq _ _ h
  push_cast at this; linear_combination this

private lemma bridge_add {a b c : FieldElement51}
    (h : ∀ i < 5, (a[i]!).val = (b[i]!).val + (c[i]!).val) :
    a.toField = b.toField + c.toField := by
  unfold FieldElement51.toField Field51_as_Nat
  have key : ∑ i ∈ Finset.range 5, 2 ^ (51 * i) * (a[i]!).val =
    ∑ i ∈ Finset.range 5, 2 ^ (51 * i) * (b[i]!).val +
    ∑ i ∈ Finset.range 5, 2 ^ (51 * i) * (c[i]!).val := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi; rw [h i hi]; ring
  exact (congrArg Nat.cast key).trans (Nat.cast_add _ _)

private lemma bridge_cond_nat {a b c : FieldElement51} {flag : subtle.Choice}
    (h : ∀ i < 5, a[i]! = if flag.val = 1#u8 then b[i]! else c[i]!) :
    Field51_as_Nat a = if flag.val = 1#u8 then Field51_as_Nat b else Field51_as_Nat c := by
  unfold Field51_as_Nat; split <;> rename_i hc
  · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
    have := h i hi; rw [if_pos hc] at this; rw [this]
  · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
    have := h i hi; rw [if_neg hc] at this; rw [this]

private lemma bridge_cond {a b c : FieldElement51} {flag : subtle.Choice}
    (h : ∀ i < 5, a[i]! = if flag.val = 1#u8 then b[i]! else c[i]!) :
    a.toField = if flag.val = 1#u8 then b.toField else c.toField := by
  unfold FieldElement51.toField; rw [bridge_cond_nat h]; split <;> rfl

private lemma p_sub_one_lt : p - 1 < p := by decide

private lemma p_sub_one_cast : (↑(p - 1) : ZMod p) = -1 := by
  rw [Nat.cast_sub (by decide : 1 ≤ p), ZMod.natCast_self, zero_sub, Nat.cast_one]

private lemma lift_fe_sq (fe : FieldElement51) (h : Field51_as_Nat fe ^ 2 % p = p - 1) :
    fe.toField ^ 2 = -1 := by
  unfold FieldElement51.toField
  have h := lift_mod_eq (Field51_as_Nat fe ^ 2) (p - 1) (by rwa [Nat.mod_eq_of_lt p_sub_one_lt])
  push_cast at h; rwa [p_sub_one_cast] at h

private lemma lift_rm_sq (rm : FieldElement51)
    (h : (Field51_as_Nat rm) ^ 2 * (a - d) % p = 1) :
    rm.toField ^ 2 * (a_val - (↑d : ZMod p)) = 1 := by
  unfold FieldElement51.toField a_val
  rw [show a = (-1 : ℤ) from rfl] at h
  have : (((↑(Field51_as_Nat rm) : ℤ) ^ 2 * (-1 - ↑d) : ℤ) : ZMod p) = 1 := by
    rw [← ZMod.intCast_mod _ p, h, Int.cast_one]
  push_cast at this; exact this

set_option maxHeartbeats 600000 in -- maxHeartbeats increased: compress has many sub-calls, progress* needs more time after Aeneas update
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
  all_goals try (intro i hi; first
      | exact h.1.Z_bounds i hi
      | exact h.1.Y_bounds i hi
      | (have := h.1.X_bounds i hi; omega)
      | (have := h.1.T_bounds i hi; omega)
      | omega)
  · intro i hi
    simp only [X_post i hi]
    split_ifs
    · have := iY_post2 i hi; omega
    · have := h.1.X_bounds i hi; omega
  have h_s1_nat := bridge_cond_nat s1_post
  have h_a_eq : U8x32_as_Nat a = Field51_as_Nat s1 % p := by
    have := a_post1; rw [Nat.ModEq, Nat.mod_eq_of_lt a_post2] at this; exact this
  -- Shared bridge: parity of s1 mod p is 0
  have h_s1_parity : Field51_as_Nat s1 % p % 2 = 0 := by
    rw [h_s1_nat]
    split <;> rename_i hc
    · -- s_is_negative = 1: s1 = s_neg, need (Field51_as_Nat s_neg % p) % 2 = 0
      have h_s_odd := s_is_negative_post.mp hc
      have h_sum := s_neg_post1
      -- Field51_as_Nat s_neg ≡ -(Field51_as_Nat s) [MOD p]
      have h_s_mod_ne : Field51_as_Nat s % p ≠ 0 := by
        intro h_zero; rw [h_zero] at h_s_odd; simp at h_s_odd
      have h_s_mod_lt : Field51_as_Nat s % p < p := Nat.mod_lt _ (by decide)
      have h_s_mod_pos : 0 < Field51_as_Nat s % p := Nat.pos_of_ne_zero h_s_mod_ne
      have h_neg_mod : Field51_as_Nat s_neg % p = p - Field51_as_Nat s % p := by
        have h1 : (Field51_as_Nat s % p + Field51_as_Nat s_neg % p) % p = 0 := by
          simp only [Nat.add_mod_mod, Nat.mod_add_mod]
          rw [Nat.ModEq] at h_sum; simpa using h_sum
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
  refine ⟨ ?_, ?_ ⟩
  · -- Main Goal 1: CompressedRistretto.IsValid
    unfold CompressedRistretto.IsValid
    sorry
  · -- Main Goal 2: compress_pure self.toPoint = U8x32_as_Nat a
    -- Name the invsqrt result and its postconditions
    rename_i _ _ _ _ _ _ x_post1 _ x_post2 x_post3 x_post4 x_post5 x_post6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    have hvalid := h.1
    have ⟨hpx, hpy⟩ := edwards.EdwardsPoint.toPoint_of_isValid hvalid
    have hZ_ne := hvalid.Z_ne_zero  -- Z.toField ≠ 0
    have hT_rel := hvalid.T_relation  -- X.toField * Y.toField = T.toField * Z.toField
    -- Mul/Sq bridges (implicit args infer x✝.2 for i1/i2 automatically)
    have hb_u1 := bridge_mul u1_post1
    have hb_u2 := bridge_mul u2_post1
    have hb_u2_sq := bridge_sq u2_sq_post1
    have hb_u1_u2_sq := bridge_mul u1_u2_sq_post1
    have hb_i1 := bridge_mul i1_post1
    have hb_i2 := bridge_mul i2_post1
    have hb_i2_T := bridge_mul i2_T_post1
    have hb_z_inv := bridge_mul z_inv_post1
    have hb_iX := bridge_mul iX_post1
    have hb_iY := bridge_mul iY_post1
    have hb_enchanted := bridge_mul enchanted_denominator_post1
    have hb_t_z_inv := bridge_mul t_z_inv_post1
    have hb_x_z_inv := bridge_mul x_z_inv_post1
    have hb_s := bridge_mul s_post1
    -- Sub/Neg bridges
    have hb_zmy := bridge_sub z_minus_y_post2
    have hb_zmy2 := bridge_sub z_minus_y2_post2
    have hb_y_neg := bridge_neg y_neg_post1
    have hb_zpy := bridge_add z_plus_y_post1
    have h_key : s1.toField = compress_s self.toPoint := by
      -- Setup: affine coordinates and IsValid properties
      set P := self.toPoint with hP_def
      -- Step 1: s1.toField = abs_edwards(s.toField) via conditional negation
      have h_s1_abs : s1.toField = abs_edwards s.toField := by
        rw [bridge_cond s1_post, bridge_neg s_neg_post1, abs_edwards, is_negative]
        by_cases hc : s_is_negative.val = 1#u8
        · rw [if_pos hc]
          have : (s.toField.val % 2 == 1) = true := by
            rw [beq_iff_eq]; unfold FieldElement51.toField;
            rw [ZMod.val_natCast]
            exact s_is_negative_post.mp hc
          simp only [this, ite_true]
        · rw [if_neg hc]
          simp only [beq_iff_eq, right_eq_ite_iff]
          intro h_odd
          exact absurd (s_is_negative_post.mpr
          (by unfold FieldElement51.toField at h_odd; rwa [ZMod.val_natCast] at h_odd)) hc
      -- Step 2: conditional assign bridges
      have hb_i21 := bridge_cond i21_post
      have hb_Y := bridge_cond Y_post
      have hb_X := bridge_cond X_post
      have hb_Y1 := bridge_cond Y1_post
      -- Step 3: projective coordinate relations
      have h_u1_proj : u1.toField = self.Z.toField ^ 2 - self.Y.toField ^ 2 := by
        rw [hb_u1, hb_zpy, hb_zmy]; ring
      have h_u1_u2_sq_val : u1_u2_sq.toField =
          (self.Z.toField ^ 2 - self.Y.toField ^ 2) *
          (self.X.toField * self.Y.toField) ^ 2 := by
        rw [hb_u1_u2_sq, hb_u2_sq, h_u1_proj, hb_u2]
      -- Step 4: QR argument — when u1_u2_sq ≠ 0, I² · u1_u2_sq = 1
      have h_I_sq_mul : u1_u2_sq.toField ≠ 0 →
          x_post1.2.toField ^ 2 * u1_u2_sq.toField = 1 := by
        intro h_ne
        have h_ne_nat : Field51_as_Nat u1_u2_sq % p ≠ 0 := by
          rwa [FieldElement51.toField, ne_eq, ZMod.natCast_eq_zero_iff,
               Nat.dvd_iff_mod_eq_zero] at h_ne
        have h_qr : ∃ x, x ^ 2 * (Field51_as_Nat u1_u2_sq % p) % p = 1 := by
          have h_sq : IsSquare u1_u2_sq.toField := by
            rw [h_u1_u2_sq_val]
            exact (h.2 : IsSquare (self.Z.toField ^ 2 - self.Y.toField ^ 2)).mul ⟨_, (sq _)⟩
          obtain ⟨r, hr⟩ := h_sq
          have hr_ne : r ≠ 0 := by intro heq; rw [heq, mul_zero] at hr; exact h_ne hr
          have h_inv : r⁻¹ ^ 2 * u1_u2_sq.toField = 1 := by rw [hr]; field_simp
          refine ⟨(r⁻¹).val, ?_⟩
          have hmod : (↑(Field51_as_Nat u1_u2_sq % p) : ZMod p) = u1_u2_sq.toField := by
            unfold FieldElement51.toField; rw [ZMod.natCast_eq_natCast_iff]
            exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
          have h_zmod : (↑((r⁻¹).val ^ 2 * (Field51_as_Nat u1_u2_sq % p)) : ZMod p) = 1 := by
            push_cast; rw [ZMod.natCast_zmod_val, hmod]; exact h_inv
          have h_val := congrArg ZMod.val h_zmod
          rw [ZMod.val_natCast, ZMod.val_one'' (by decide : p ≠ 1)] at h_val
          exact h_val
        have h_post := (x_post5 ⟨h_ne_nat, h_qr⟩).2
        -- Lift Nat % p equation to ZMod
        have hmm : ∀ a, (a % p) ≡ a [MOD p] := fun a => by
          exact Nat.mod_eq_of_lt (Nat.mod_lt a (by decide))
        have h_modeq : Field51_as_Nat x_post1.2 ^ 2 * Field51_as_Nat u1_u2_sq ≡ 1 [MOD p] :=
          ((hmm _).symm.pow 2).mul (hmm _).symm |>.trans (by exact h_post)
        unfold FieldElement51.toField
        have := lift_mod_eq _ _ h_modeq; push_cast at this; exact this
      -- Step 5: The squared equality (the main algebraic content)
      have h_sq_eq : s.toField ^ 2 =
          (compress_den_inv P * (1 - compress_y_final P)) ^ 2 := by
        -- Step 1: Lift constant squared facts to ZMod
        have h_fe_sq := lift_fe_sq fe fe_post1
        have h_rm_sq := lift_rm_sq ristretto_magic ristretto_magic_post1
        -- Affine ↔ projective bridge for P
        have hpx' : P.x = self.X.toField / self.Z.toField := by rw [hP_def]; exact hpx
        have hpy' : P.y = self.Y.toField / self.Z.toField := by rw [hP_def]; exact hpy
        -- Key link: compress_u1 P * compress_u2 P² = u1_u2_sq / Z⁶
        have h_aff : compress_u1 P * compress_u2 P ^ 2 =
            u1_u2_sq.toField / self.Z.toField ^ 6 := by
          unfold compress_u1 compress_u2; rw [hpx', hpy', h_u1_u2_sq_val]; field_simp; ring
        by_cases hd : u1_u2_sq.toField = 0
        · -- Degenerate: I = 0, so s = 0 and compress_den_inv P = 0
          have h_nat : Field51_as_Nat u1_u2_sq % p = 0 := by
            rwa [FieldElement51.toField, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at hd
          have hI0 : x_post1.2.toField = 0 := by
            rw [FieldElement51.toField, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
            exact (x_post4 h_nat).2
          -- LHS: I=0 → i1=i2=0 → i21=0 → s=0
          have hi2_0 : i2.toField = 0 := by rw [hb_i2, hI0, zero_mul]
          have hs0 : s.toField = 0 := by
            rw [hb_s, hb_i21]; split_ifs
            · rw [hb_enchanted, hb_i1, hI0, zero_mul, zero_mul, zero_mul]
            · rw [hi2_0, zero_mul]
          -- RHS: compress_invsqrt P = 0 → compress_den_inv P = 0
          have hJ0 : compress_invsqrt P = 0 := by
            unfold compress_invsqrt; rw [h_aff, hd, zero_div, inv_sqrt_checked_zero]
          have hdi0 : compress_den_inv P = 0 := by
            unfold compress_den_inv compress_den1 compress_den2; rw [hJ0]; split_ifs <;> ring
          rw [hs0, hdi0]; ring
        · -- Nondegenerate: J² = I²·Z⁶, both sides equal
          have h_ne_aff : compress_u1 P * compress_u2 P ^ 2 ≠ 0 := by
            rw [h_aff]; exact div_ne_zero hd (pow_ne_zero _ hZ_ne)
          have h_isq : IsSquare (compress_u1 P * compress_u2 P ^ 2) := by
            rw [h_aff, h_u1_u2_sq_val]
            obtain ⟨w, hw⟩ := (h.2 : IsSquare (self.Z.toField ^ 2 - self.Y.toField ^ 2))
            exact ⟨w * (self.X.toField * self.Y.toField) / self.Z.toField ^ 3,
              by rw [hw]; field_simp⟩
          have hJ_sq : compress_invsqrt P ^ 2 * (compress_u1 P * compress_u2 P ^ 2) = 1 := by
            unfold compress_invsqrt; exact inv_sqrt_checked_sq_mul _ h_isq h_ne_aff
          -- Step B: J² = I²·Z⁶ and compress_z_inv P = 1
          set I := x_post1.2.toField with hI_def
          set Z := self.Z.toField with hZ_def
          have hJ_I : compress_invsqrt P ^ 2 = I ^ 2 * Z ^ 6 := by
            have hI_u := h_I_sq_mul hd
            have hJ_u : compress_invsqrt P ^ 2 * u1_u2_sq.toField = Z ^ 6 := by
              rwa [h_aff, ← mul_div_assoc, div_eq_iff (pow_ne_zero 6 hZ_ne), one_mul] at hJ_sq
            have : u1_u2_sq.toField * (compress_invsqrt P ^ 2 - I ^ 2 * Z ^ 6) = 0 := by
              linear_combination hJ_u - hI_u * Z ^ 6
            exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hd)
          have hz_inv_one : compress_z_inv P = 1 := by
            have : compress_z_inv P =
                compress_invsqrt P ^ 2 * (compress_u1 P * compress_u2 P ^ 2) := by
              unfold compress_z_inv compress_den1 compress_den2 compress_u2; ring
            rw [this, hJ_sq]
          -- Step C: z_inv.toField * Z = 1 (key for flag matching)
          have h_z_inv_mul : z_inv.toField * Z = 1 := by
            have hI := h_I_sq_mul hd; rw [h_u1_u2_sq_val] at hI
            rw [hb_z_inv, hb_i1, hb_i2_T, hb_i2, h_u1_proj, hb_u2]
            linear_combination hI - I ^ 2 * (Z ^ 2 - self.Y.toField ^ 2) *
              (self.X.toField * self.Y.toField) * hT_rel
          sorry
      -- Conclude: s1 = abs(s) = abs(compress_den_inv * (1 - y_final)) = compress_s P
      rw [h_s1_abs]; unfold compress_s
      exact abs_edwards_eq_of_sq_eq h_sq_eq
    -- Goal 2 conclusion: compress_pure self.toPoint = U8x32_as_Nat a
    change compress_pure self.toPoint = U8x32_as_Nat a
    unfold compress_pure
    rw [← h_key]
    unfold FieldElement51.toField
    rw [ZMod.val_natCast]
    exact h_a_eq.symm

end curve25519_dalek.ristretto.RistrettoPoint
