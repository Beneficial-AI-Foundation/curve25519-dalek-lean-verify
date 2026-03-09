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
  unfold FieldElement51.toField
  simpa only [Nat.cast_mul] using lift_mod_eq _ _ h

private lemma bridge_sq {a b : FieldElement51}
    (h : Field51_as_Nat a ≡ Field51_as_Nat b ^ 2 [MOD p]) :
    a.toField = b.toField ^ 2 := by
  unfold FieldElement51.toField
  simpa only [Nat.cast_pow] using lift_mod_eq _ _ h

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

private lemma flag_eq_true_iff_is_negative_of_val {flag : subtle.Choice} {n : Nat} {x : ZMod p}
    (hflag : flag.val = 1#u8 ↔ n % 2 = 1) (hx : n = x.val) :
    flag.val = 1#u8 ↔ is_negative x = true := by
  refine ⟨?_, ?_ ⟩
  · intro hf
    unfold is_negative
    rw [beq_iff_eq, ← hx]; exact hflag.mp hf
  · intro hneg
    exact hflag.mpr (by
      unfold is_negative at hneg; rw [beq_iff_eq] at hneg; rwa [← hx] at hneg)

private lemma flag_eq_true_iff_is_negative_of_neg_val
    {flag : subtle.Choice} {n : Nat} {x : ZMod p}
    (hflag : flag.val = 1#u8 ↔ n % 2 = 1) (hx : n = (-x).val) (hx_ne : x ≠ 0) :
    flag.val = 1#u8 ↔ is_negative x = false := by
  have hxv_ne : x.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
  have hxlt : x.val < p := x.val_lt
  have hxpos : 0 < x.val := Nat.pos_of_ne_zero hxv_ne
  have hp_odd : p % 2 = 1 := by decide
  have hneg_val : (-x).val = p - x.val := by
    rw [ZMod.neg_val]; exact if_neg hx_ne
  refine ⟨?_, ?_⟩
  · intro hf
    unfold is_negative
    rw [beq_eq_false_iff_ne]
    have hneg : (-x).val % 2 = 1 := by
      have : n % 2 = 1 := hflag.mp hf; rwa [hx] at this
    rw [hneg_val] at hneg
    exact fun h => by omega
  · intro hneg
    apply hflag.mpr
    unfold is_negative at hneg
    rw [beq_eq_false_iff_ne] at hneg
    rw [hx, hneg_val]
    omega

private lemma cond_neg_scale_of_flag_match (Z y x : ZMod p) (flag : subtle.Choice)
    (hflag : flag.val = 1#u8 ↔ is_negative x = true) :
    (if flag.val = 1#u8 then -(Z * y) else Z * y) =
      Z * (if is_negative x = true then -y else y) := by
  cases hix : is_negative x with
  | false =>
      have hf : flag.val ≠ 1#u8 := by
        intro hf
        have : is_negative x = true := hflag.mp hf
        rw [hix] at this
        cases this
      rw [if_neg hf, if_neg (by decide : ¬ false = true)]
  | true =>
      have hf : flag.val = 1#u8 := hflag.mpr hix
      rw [if_pos hf, if_pos (by decide : true = true)]
      ring

private lemma cond_neg_scale_of_neg_flag_match (Z y x : ZMod p) (flag : subtle.Choice)
    (hflag : flag.val = 1#u8 ↔ is_negative x = false) :
    (if flag.val = 1#u8 then -(Z * -y) else Z * -y) =
      Z * (if is_negative x = true then -y else y) := by
  cases hix : is_negative x with
  | false =>
      have hf : flag.val = 1#u8 := hflag.mpr hix
      rw [if_pos hf, if_neg (by decide : ¬ false = true)]
      ring
  | true =>
      have hf : flag.val ≠ 1#u8 := by
        intro hf
        have : is_negative x = false := hflag.mp hf
        rw [hix] at this
        cases this
      rw [if_neg hf, if_pos (by decide : true = true)]

private lemma lift_fe_sq (fe : FieldElement51) (h : Field51_as_Nat fe ^ 2 % p = p - 1) :
    fe.toField ^ 2 = -1 := by
  unfold FieldElement51.toField
  have h := lift_mod_eq (Field51_as_Nat fe ^ 2) (p - 1) (by rwa [Nat.mod_eq_of_lt (show p - 1 < p from by decide)])
  push_cast at h; rwa [p_sub_one_cast] at h

private lemma lift_rm_sq (rm : FieldElement51)
    (h : (Field51_as_Nat rm) ^ 2 * (a - d) % p = 1) :
    rm.toField ^ 2 * (a_val - (↑d : ZMod p)) = 1 := by
  unfold FieldElement51.toField a_val
  rw [show a = (-1 : ℤ) from rfl] at h
  have : (((↑(Field51_as_Nat rm) : ℤ) ^ 2 * (-1 - ↑d) : ℤ) : ZMod p) = 1 := by
    rw [← ZMod.intCast_mod _ p, h, Int.cast_one]
  push_cast at this; exact this

set_option maxHeartbeats 800000 in -- maxHeartbeats increased: compress has many sub-calls, progress* needs more time after Aeneas update
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
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt a_post2] using a_post1
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
          rw [Nat.ModEq] at h_sum; simpa only [Nat.zero_mod] using h_sum
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
    simpa only [h_a_eq] using h_s1_parity
  -- Build the shared implementation-to-pure bridge once.
  -- Both final goals consume h_key : s1.toField = compress_s self.toPoint.
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
      have hpx' : P.x = self.X.toField / self.Z.toField := by
        simpa only [hP_def] using hpx
      have hpy' : P.y = self.Y.toField / self.Z.toField := by
        simpa only [hP_def] using hpy
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
        set I := x_post1.2.toField
        set Z := self.Z.toField
        have hJ_I : compress_invsqrt P ^ 2 = I ^ 2 * Z ^ 6 := by
          have hI_u := h_I_sq_mul hd
          have hJ_u : compress_invsqrt P ^ 2 * u1_u2_sq.toField = Z ^ 6 := by
            rwa [h_aff, ← mul_div_assoc, div_eq_iff (pow_ne_zero 6 hZ_ne), one_mul] at hJ_sq
          have : u1_u2_sq.toField * (compress_invsqrt P ^ 2 - I ^ 2 * Z ^ 6) = 0 := by
            linear_combination hJ_u - hI_u * Z ^ 6
          exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hd)
        have hz_inv_one : compress_z_inv P = 1 := compress_z_inv_eq_one P hJ_sq
        -- Step C: z_inv.toField * Z = 1 (key for flag matching)
        have h_z_inv_mul : z_inv.toField * Z = 1 := by
          have hI := h_I_sq_mul hd; rw [h_u1_u2_sq_val] at hI
          rw [hb_z_inv, hb_i1, hb_i2_T, hb_i2, h_u1_proj, hb_u2]
          linear_combination hI - I ^ 2 * (Z ^ 2 - self.Y.toField ^ 2) *
            (self.X.toField * self.Y.toField) * hT_rel
        have h_t_z_inv : t_z_inv.toField = P.x * P.y := by
          rw [show P.x = self.X.toField / Z from hpx, show P.y = self.Y.toField / Z from hpy,
              hb_t_z_inv]
          field_simp
          linear_combination self.T.toField * Z * h_z_inv_mul - hT_rel
        have h_rotate : rotate.val = 1#u8 ↔ compress_rotate P = true := by
          have h_val := congrArg ZMod.val h_t_z_inv
          simp only [FieldElement51.toField, ZMod.val_natCast] at h_val
          unfold compress_rotate is_negative
          rw [hz_inv_one, mul_one]; simp only [beq_iff_eq]
          simpa only [h_val] using rotate_post
        -- Step D: s = i21 * (Z - Y1)
        have h_s_proj : s.toField = i21.toField * (Z - Y1.toField) := by
          rw [hb_s, hb_zmy2]
        -- Step E: rm² = iad²
        have h_rm_iad : ristretto_magic.toField ^ 2 = invsqrt_a_minus_d ^ 2 := by
          have had_ne : a_val - (↑d : ZMod p) ≠ 0 := by
            intro heq; rw [heq, mul_zero] at h_rm_sq; exact zero_ne_one h_rm_sq
          exact mul_right_cancel₀ had_ne (h_rm_sq.trans iad_sq.symm)
        -- Scaling identities (projective ↔ affine)
        have hX_scale : self.X.toField = Z * P.x := by rw [hpx']; field_simp
        have hY_scale : self.Y.toField = Z * P.y := by rw [hpy']; field_simp
        have h_u1_aff : u1.toField = Z ^ 2 * compress_u1 P := by
          rw [h_u1_proj, hY_scale]; unfold compress_u1; ring
        have h_u2_aff : u2.toField = Z ^ 2 * compress_u2 P := by
          rw [hb_u2, hX_scale, hY_scale]; unfold compress_u2; ring
        -- Y1 = Z · compress_y_final P (branch-independent)
        -- fe = ±sqrt_m1; when fe = -sqrt_m1 in the rotate case, double negation compensates
        have h_fe_or : fe.toField = sqrt_m1 ∨ fe.toField = -sqrt_m1 := by
          have : (fe.toField - sqrt_m1) * (fe.toField + sqrt_m1) = 0 := by
            have : fe.toField ^ 2 = sqrt_m1 ^ 2 := by rw [h_fe_sq, sqrt_m1_sq]
            linear_combination this
          rcases mul_eq_zero.mp this with h | h
          · left; linear_combination h
          · right; linear_combination h
        have h_Y1_proj : Y1.toField = Z * compress_y_final P := by
          rw [hb_Y1, hb_y_neg, compress_y_final]
          by_cases hr : rotate.val = 1#u8
          · -- ROTATE case
            have hrot := h_rotate.mp hr
            rw [hb_Y, if_pos hr, hb_iX, hX_scale,
                compress_x_prime, if_pos hrot, compress_y_prime, if_pos hrot,
                hz_inv_one, mul_one]
            -- x_z_inv.toField = P.y * fe.toField (X' = iY, z_inv·Z = 1)
            have h_xzinv : x_z_inv.toField = P.y * fe.toField := by
              rw [hb_x_z_inv, hb_X, if_pos hr, hb_iY, hY_scale]
              linear_combination P.y * fe.toField * h_z_inv_mul
            have h_xzinv_val : Field51_as_Nat x_z_inv % p = (P.y * fe.toField).val := by
              have := congrArg ZMod.val h_xzinv
              simp only [FieldElement51.toField, ZMod.val_natCast] at this; exact this
            -- P.y ≠ 0 and sqrt_m1 ≠ 0 (rotate implies P.x*P.y is negative)
            have h_py_ne : P.y ≠ 0 := by
              intro h0; have : compress_rotate P = false := by
                unfold compress_rotate; rw [hz_inv_one, mul_one, h0, mul_zero]; rfl
              exact absurd hrot (by rw [this]; decide)
            have h_sm1_ne : (sqrt_m1 : ZMod p) ≠ 0 := by
              intro h; have hsq := sqrt_m1_sq; rw [h, zero_pow (by norm_num)] at hsq
              exact absurd hsq (by decide)
            rcases h_fe_or with hfe | hfe
            · -- fe = sqrt_m1: direct value & parity match
              rw [hfe] at h_xzinv_val ⊢
              have h_sign_match : y_sign.val = 1#u8 ↔ is_negative (P.y * sqrt_m1) = true :=
                flag_eq_true_iff_is_negative_of_val y_sign_post h_xzinv_val
              simpa only [mul_assoc] using
                cond_neg_scale_of_flag_match Z (P.x * sqrt_m1) (P.y * sqrt_m1) y_sign
                  h_sign_match
            · -- fe = -sqrt_m1: parity flips, double negation compensates
              rw [hfe] at h_xzinv_val ⊢
              have h_pysm1_ne : P.y * sqrt_m1 ≠ 0 := mul_ne_zero h_py_ne h_sm1_ne
              have h_xzinv_neg_val : Field51_as_Nat x_z_inv % p = (-(P.y * sqrt_m1)).val := by
                rw [show P.y * -sqrt_m1 = -(P.y * sqrt_m1) from by ring] at h_xzinv_val
                exact h_xzinv_val
              have h_sign_match : y_sign.val = 1#u8 ↔ is_negative (P.y * sqrt_m1) = false :=
                flag_eq_true_iff_is_negative_of_neg_val y_sign_post h_xzinv_neg_val h_pysm1_ne
              simpa only [mul_assoc, mul_neg, neg_mul, neg_neg] using
                cond_neg_scale_of_neg_flag_match Z (P.x * sqrt_m1) (P.y * sqrt_m1) y_sign
                  h_sign_match
          · -- NO-ROTATE case: Y = self.Y, no fe involvement
            rw [hb_Y, if_neg hr, hY_scale,
                compress_x_prime, if_neg (fun h => hr (h_rotate.mpr h)),
                compress_y_prime, if_neg (fun h => hr (h_rotate.mpr h)),
                hz_inv_one, mul_one]
            have h_xzinv_val : Field51_as_Nat x_z_inv % p = P.x.val := by
              have : x_z_inv.toField = P.x := by
                rw [hb_x_z_inv, hb_X, if_neg hr, hX_scale]
                linear_combination P.x * h_z_inv_mul
              have := congrArg ZMod.val this
              simp only [FieldElement51.toField, ZMod.val_natCast] at this; exact this
            have h_sign_match : y_sign.val = 1#u8 ↔ is_negative P.x = true :=
              flag_eq_true_iff_is_negative_of_val y_sign_post h_xzinv_val
            simpa only [mul_assoc] using cond_neg_scale_of_flag_match Z P.y P.x y_sign h_sign_match
        have h_zmy_sq :
            (Z - Y1.toField) ^ 2 = Z ^ 2 * (1 - compress_y_final P) ^ 2 := by
          rw [h_Y1_proj]; ring
        -- Denominator square identity: i21² = compress_den_inv² / Z²
        have h_i2_sq : i2.toField ^ 2 = compress_den2 P ^ 2 / Z ^ 2 := by
          rw [eq_div_iff (pow_ne_zero 2 hZ_ne)]
          have h1 : i2.toField ^ 2 * Z ^ 2 = I ^ 2 * Z ^ 6 * compress_u2 P ^ 2 := by
            rw [hb_i2, h_u2_aff]; ring
          rw [h1, ← hJ_I]; unfold compress_den2; ring
        have h_i1_sq : i1.toField ^ 2 = compress_den1 P ^ 2 / Z ^ 2 := by
          rw [eq_div_iff (pow_ne_zero 2 hZ_ne)]
          have h1 : i1.toField ^ 2 * Z ^ 2 = I ^ 2 * Z ^ 6 * compress_u1 P ^ 2 := by
            rw [hb_i1, h_u1_aff]; ring
          rw [h1, ← hJ_I]; unfold compress_den1; ring
        have h_ench_sq : enchanted_denominator.toField ^ 2 =
            (compress_den1 P * invsqrt_a_minus_d) ^ 2 / Z ^ 2 := by
          rw [eq_div_iff (pow_ne_zero 2 hZ_ne)]
          have h_exp : enchanted_denominator.toField ^ 2 * Z ^ 2 =
              i1.toField ^ 2 * ristretto_magic.toField ^ 2 * Z ^ 2 := by
            rw [hb_enchanted]; ring
          rw [h_exp, h_rm_iad]
          have h_exp2 : i1.toField ^ 2 * invsqrt_a_minus_d ^ 2 * Z ^ 2 =
              I ^ 2 * Z ^ 6 * compress_u1 P ^ 2 * invsqrt_a_minus_d ^ 2 := by
            rw [hb_i1, h_u1_aff]; ring
          rw [h_exp2, ← hJ_I]; unfold compress_den1; ring
        have h_i21_sq : i21.toField ^ 2 = compress_den_inv P ^ 2 / Z ^ 2 := by
          rw [hb_i21]; split_ifs with hr
          · simpa only [compress_den_inv, if_pos (h_rotate.mp hr)] using h_ench_sq
          · simpa only [compress_den_inv, if_neg (fun h => hr (h_rotate.mpr h))] using h_i2_sq
        -- Close the squared equality via calc
        rw [h_s_proj]
        calc (i21.toField * (Z - Y1.toField)) ^ 2
            = i21.toField ^ 2 * (Z - Y1.toField) ^ 2 := by ring
          _ = (compress_den_inv P ^ 2 / Z ^ 2) *
              (Z ^ 2 * (1 - compress_y_final P) ^ 2) := by
              rw [h_i21_sq, h_zmy_sq]
          _ = (compress_den_inv P * (1 - compress_y_final P)) ^ 2 := by
              field_simp;
    -- Conclude: s1 = abs(s) = abs(compress_den_inv * (1 - y_final)) = compress_s P
    rw [h_s1_abs]; unfold compress_s
    exact abs_edwards_eq_of_sq_eq h_sq_eq
  refine ⟨?goal1, ?goal2⟩
  case goal2 =>
    -- Main Goal 2: compress_pure self.toPoint = U8x32_as_Nat a
    change compress_pure self.toPoint = U8x32_as_Nat a
    simpa only [compress_pure] using ((congrArg ZMod.val h_key).symm.trans h_a_eq.symm)
  case goal1 =>
    -- Main Goal 1: CompressedRistretto.IsValid
    unfold CompressedRistretto.IsValid
    -- Extract evenness from validity
    have h_even : IsEven self.toPoint :=
      (EdwardsPoint_IsSquare_iff_IsEven self hvalid).mp h.2
    -- Step 1: decompress_step1 a succeeds, yielding compress_s P
    have h_s_cast : (↑(U8x32_as_Nat a) : ZMod p) = compress_s self.toPoint := by
      rw [h_a_eq, ZMod.natCast_mod, ← h_key]; rfl
    have h_step1 : decompress_step1 a = some (compress_s self.toPoint) := by
      unfold decompress_step1
      have h1 : ¬(p ≤ U8x32_as_Nat a) := Nat.not_le.mpr a_post2
      have h2 : U8x32_as_Nat a % 2 = 0 := h_a_parity
      simp only [ge_iff_le, h1, decide_false, h2, bne_self_eq_false, Bool.false_or,
        ↓reduceIte, h_s_cast, Bool.false_eq_true, ↓reduceIte]
    -- Step 2: decompress_step2 (compress_s P) succeeds (pure roundtrip)
    obtain ⟨pt, hpt⟩ := decompress_step2_compress_s self.toPoint h_even
    exact ⟨pt, by simpa only [decompress_pure, h_step1, Option.bind_some] using hpt⟩

end curve25519_dalek.ristretto.RistrettoPoint
