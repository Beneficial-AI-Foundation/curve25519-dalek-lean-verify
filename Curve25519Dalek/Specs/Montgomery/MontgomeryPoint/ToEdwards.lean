/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Edwards.CompressedEdwardsY.Decompress
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.MINUS_ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq
import Curve25519Dalek.Math.Montgomery.Representation

/-! # Spec Theorem for `MontgomeryPoint::to_edwards`

Specification and proof for `MontgomeryPoint::to_edwards`.

This function attempts to convert a MontgomeryPoint (u-coordinate only) to an
EdwardsPoint on the twisted Edwards curve, using the birational map
y = (u-1)/(u+1), followed by Edwards decompression with a specified sign bit.

**Source**: curve25519-dalek/src/montgomery.rs:224-253

-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.montgomery.MontgomeryPoint
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
natural language description:

    Converts a MontgomeryPoint (u-coordinate only) to an EdwardsPoint using the
    birational map y = (u-1)/(u+1) (mod p), where p = 2^255 - 19.
    Special case: when u ≡ -1 (mod p), returns None (point is on the twist).
    Otherwise, computes y, encodes it with the specified sign bit, and decompresses
    to obtain a full EdwardsPoint.

natural language specs:

    When the function returns Some(ep):
      - ep.Z is invertible in the field (invert ep.Z = ok Z_inv for some Z_inv)
      - The affine Edwards y-coordinate y = ep.Y / ep.Z satisfies the birational map:
          y * (u + 1) ≡ u - 1 (mod p)
        where u = U8x32_as_Nat mp % 2^255

    where p = 2^255 - 19
-/

@[progress]
lemma ONE_bounds_spec : ONE ⦃ result => Field51_as_Nat result = 1 ∧ ∀ i < 5, result[i]!.val < 2 ^ 53 ⦄ := by
  unfold ONE from_limbs
  simp only [spec_ok]
  decide


@[progress]
theorem to_edwards_spec (mp : MontgomeryPoint) (sign : U8) :
      to_edwards mp sign ⦃ result =>
        (∀ ep, result = some ep →
          ∃ Z_inv,
            field.FieldElement51.invert ep.Z = ok Z_inv ∧
            let u := U8x32_as_Nat mp % 2^255
            let y := Field51_as_Nat ep.Y * Field51_as_Nat Z_inv % p  -- Affine y = Y/Z
            (y * ((u + 1) % p)) % p = ((u + p - 1) % p) % p)
      ⦄ := by

  unfold to_edwards
  progress*
  unfold FieldElement51.Insts.CoreCmpPartialEqFieldElement51.eq
  progress*  -- This eliminates ct_eq

  -- have h_ONE_bounds : ∀ i < 5, FieldElement51.ONE[i]!.val < 2 ^ 54 := by
  --   intro i hi
  --   unfold FieldElement51.ONE
  --   interval_cases i <;> decide

  -- have h_MINUS_ONE_bounds : ∀ i < 5, FieldElement51.MINUS_ONE[i]!.val < 2 ^ 54 := by
  --   intro i hi
  --   unfold FieldElement51.MINUS_ONE
  --   interval_cases i <;> decide

  -- have h_u_sub_bounds : ∀ i < 5, u[i]!.val < 2 ^ 63 := by
  --   intro i hi
  --   have := u_post_2 i hi
  --   omega

  -- have h_ONE_sub_bounds : ∀ i < 5, FieldElement51.ONE[i]!.val < 2 ^ 54 := by
  --   intro i hi
  --   have := h_ONE_bounds i hi
  --   omega

  -- have h_u_add_bounds : ∀ i < 5, u[i]!.val < 2 ^ 53 := by
  --   intro i hi
  --   have := u_post_2 i hi
  --   omega

  unfold Bool.Insts.CoreConvertFromChoice.from
  simp
  split
  · simp
  · progress*
    -- · sorry
    -- ·
      -- sorry
      -- grind only
    · have h_res := result_post1 result_post2
      sorry
    --   obtain ⟨Z_inv, x_val, y_val, x_is_neg, h_Zinv, h_X, h_Y, h_neg, h_curve, h_y_val, h_sign, h_T⟩ := h_res
      -- use Z_inv
      -- constructor
      -- · exact h_Zinv
    --   ·
    --     have h_expand : Field51_as_Nat fe1 = Field51_as_Nat u + Field51_as_Nat FieldElement51.ONE := by
    --         unfold Field51_as_Nat
    --         rw [← Finset.sum_add_distrib]
    --         apply Finset.sum_congr rfl
    --         intro i hi
    --         have h_limb := fe1_post_1 i (Finset.mem_range.mp hi)
    --         simp only at h_limb
    --         rw [h_limb]
    --         ring
    --     have h_ONE : Field51_as_Nat FieldElement51.ONE = 1 := FieldElement51.ONE_spec
    --     have h_affine_y : Field51_as_Nat res_post_2.Y * Field51_as_Nat Z_inv % p = y_val := h_Y
    --     have h_bytes_equiv : U8x32_as_Nat y_bytes1 % 2^255 % p = U8x32_as_Nat y_bytes % 2^255 % p := by
    --       rw [y_bytes1_post]
    --       have hb31 : (y_bytes).val[31]!.val < 128 := by
    --         have h255 : U8x32_as_Nat y_bytes < 2^255 := by
    --           have : p < 2^255 := by unfold p; norm_num
    --           linarith [y_bytes_post_2]
    --         have := high_bit_zero_of_lt_255 y_bytes h255
    --         omega

    --       have coerce_eq : (↑y_bytes : List U8)[31]! = y_bytes[31]! := by
    --         simp only [Array.getElem!_Nat_eq]

    --       have h_i1_eq : i1.val = y_bytes[31]!.val := by
    --         have h := congrArg UScalar.val i1_post
    --         grind only

    --       have h_i1_lt : i1.val < 128 := by
    --         grind only
    --       have h_i2_lo : i2.val % 128 = i1.val := by
    --         have h_xor_lo : (i2.bv &&& 0x7F#8) = (i1.bv &&& 0x7F#8) := by
    --           simp [i2_post_2, i_post_2]
    --           bv_decide
    --         have h_mod_i2 : i2.val % 128 = (i2.bv &&& 0x7F#8).toNat := by
    --           change i2.bv.toNat % 128 = (i2.bv &&& 0x7F#8).toNat
    --           simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    --           have hmask := Nat.and_two_pow_sub_one_eq_mod i2.bv.toNat 7
    --           norm_num at hmask; linarith
    --         have h_mod_i1 : (i1.bv &&& 0x7F#8).toNat = i1.val := by
    --           change (i1.bv &&& 0x7F#8).toNat = i1.bv.toNat
    --           simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    --           have hmask := Nat.and_two_pow_sub_one_eq_mod i1.bv.toNat 7
    --           have hlt : i1.bv.toNat < 128 := h_i1_lt
    --           norm_num at hmask; linarith [Nat.mod_eq_of_lt hlt]
    --         rw [h_mod_i2, h_xor_lo, h_mod_i1]
    --       have h_i2_mod : i2.val % 128 = (↑y_bytes)[31]!.val := by rw [h_i2_lo, h_i1_eq]

    --       have h_orig_eq : U8x32_as_Nat y_bytes =
    --           (∑ j ∈ Finset.range 31, 2^(8*j) * (y_bytes.val[j]!).val) + 2^248 * (↑y_bytes)[31]!.val := by
    --         unfold U8x32_as_Nat
    --         rw [Finset.sum_range_succ, show (8:Nat) * 31 = 248 from by norm_num]
    --         simp [Array.getElem!_Nat_eq]

    --       have h_set_eq : U8x32_as_Nat (y_bytes.set 31#usize i2) =
    --           (∑ j ∈ Finset.range 31, 2^(8*j) * (y_bytes.val[j]!).val) + 2^248 * i2.val := by
    --         unfold U8x32_as_Nat
    --         rw [Finset.sum_range_succ, show (8:Nat) * 31 = 248 from by norm_num]
    --         simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
    --         have h_idx : (↑(31#usize) : ℕ) = 31 := by native_decide
    --         rw [h_idx]
    --         rw [congrArg UScalar.val (List.getElem!_set (↑y_bytes : List U8) 31 i2
    --           (by simp [y_bytes.property]))]
    --         have h_eq : ∑ j ∈ Finset.range 31, 2^(8*j) *
    --                 UScalar.val ((↑y_bytes : List U8).set 31 i2)[j]! =
    --             ∑ j ∈ Finset.range 31, 2^(8*j) *
    --                 UScalar.val (↑y_bytes : List U8)[j]! :=
    --           Finset.sum_congr rfl (fun j hj => congrArg (2^(8*j) * ·)
    --             (congrArg UScalar.val (List.getElem!_set_ne (↑y_bytes : List U8) 31 j i2
    --               (Or.inr (Or.inr (Or.inr (Finset.mem_range.mp hj)))))))
    --         grind only

    --       rw [h_set_eq, h_orig_eq]
    --       set S := ∑ j ∈ Finset.range 31, 2^(8*j) * (y_bytes.val[j]!).val
    --       set v := (↑y_bytes)[31]!.val
    --       have h_expand : S + 2^248 * i2.val = (S + 2^248 * v) + 2^255 * (i2.val / 128) := by
    --         have h_decomp : i2.val = v + 128 * (i2.val / 128) := by omega  -- from h_i2_mod
    --         calc S + 2^248 * i2.val
    --             = S + 2^248 * (v + 128 * (i2.val / 128)) := by grind only
    --           _ = (S + 2^248 * v) + 2^248 * 128 * (i2.val / 128) := by ring
    --           _ = (S + 2^248 * v) + 2^255 * (i2.val / 128) := by norm_num
    --       rw [h_expand, Nat.add_mul_mod_self_left]

    --     have h_bytes_mod : U8x32_as_Nat y_bytes % 2^255 % p = U8x32_as_Nat y_bytes % p := by
    --       have hp : p < 2^255 := by
    --         unfold p
    --         norm_num
    --       have hlt : U8x32_as_Nat y_bytes < p := y_bytes_post_2
    --       have h_lt_255 : U8x32_as_Nat y_bytes < 2^255 := by omega
    --       rw [Nat.mod_eq_of_lt h_lt_255]

    --     have h_y_bytes : U8x32_as_Nat y_bytes % p = Field51_as_Nat y % p := by
    --       exact y_bytes_post_1

    --     have h_y_eq : Field51_as_Nat y % p = (Field51_as_Nat fe * Field51_as_Nat fe2) % p := by
    --       exact y_post_1

    --     have h_y_val_eq : y_val % p = (Field51_as_Nat fe * Field51_as_Nat fe2) % p := by
    --       calc y_val % p
    --           = U8x32_as_Nat y_bytes1 % 2^255 % p := h_y_val
    --         _ = U8x32_as_Nat y_bytes % 2^255 % p := h_bytes_equiv
    --         _ = U8x32_as_Nat y_bytes % p := h_bytes_mod
    --         _ = Field51_as_Nat y % p := h_y_bytes
    --         _ = (Field51_as_Nat fe * Field51_as_Nat fe2) % p := h_y_eq

    --     have h_fe1_ne_zero : Field51_as_Nat fe1 % p ≠ 0 := by
    --       intro h_contra
    --       have h_eq_bytes : u.to_bytes = FieldElement51.MINUS_ONE.to_bytes := by
    --         have h1 : (Field51_as_Nat u + 1) % p = 0 := by
    --           have tmp_h: Field51_as_Nat fe1 = (Field51_as_Nat u) +1 := by
    --             rw [h_expand, h_ONE]
    --           grind only

    --         have h2 :
    --         Field51_as_Nat u % p = p - 1 := by
    --           rw [Nat.add_mod] at h1
    --           have hp : 0 < p := by decide
    --           have hlt : Field51_as_Nat u % p < p := Nat.mod_lt _ hp
    --           have h2 : Field51_as_Nat u % p + 1 = p := by
    --             obtain h1modp: 1 % p = 1 := by decide
    --             rw [h1modp] at h1
    --             have hdvd : p ∣ (Field51_as_Nat u % p + 1) := Nat.dvd_of_mod_eq_zero h1
    --             have hge : p ≤ Field51_as_Nat u % p + 1 := Nat.le_of_dvd (by omega) hdvd
    --             omega
    --           have : Field51_as_Nat u % p = p - 1 := by
    --             omega
    --           exact this
    --         have h3 :
    --         Field51_as_Nat u % p =
    --         Field51_as_Nat FieldElement51.MINUS_ONE % p := by
    --           simp only [FieldElement51.MINUS_ONE_spec, Nat.self_sub_mod]
    --           exact h2

    --         have h4 :
    --         Field51_as_Nat u =
    --         Field51_as_Nat FieldElement51.MINUS_ONE := by
    --             have hu_lt : Field51_as_Nat u < 2^255 := by
    --               simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.sum_range_zero]
    --               have h0 := u_post_2 0 (by norm_num)
    --               have h1 := u_post_2 1 (by norm_num)
    --               have h2' := u_post_2 2 (by norm_num)
    --               have h3' := u_post_2 3 (by norm_num)
    --               have h4' := u_post_2 4 (by norm_num)
    --               simp only [Array.getElem!_Nat_eq, Nat.zero_add] at *
    --               omega
    --             have hp_val : p = 2^255 - 19 := by rfl
    --             have hMINUS_ONE_val : Field51_as_Nat FieldElement51.MINUS_ONE = p - 1 :=
    --               FieldElement51.MINUS_ONE_spec
    --             grind only
    --         obtain ⟨ub, hub_eq, hub_rest⟩ := spec_imp_exists (to_bytes_spec u)
    --         obtain ⟨hub_mod, hub_lt⟩ := hub_rest
    --         obtain ⟨mb, hmb_eq, hmb_rest⟩ := spec_imp_exists (to_bytes_spec MINUS_ONE)
    --         obtain ⟨hmb_mod, hmb_lt⟩ := hmb_rest
    --         rw [hub_eq, hmb_eq]
    --         simp only [ok.injEq]
    --         apply U8x32_as_Nat_injective
    --         have h_u_canon : U8x32_as_Nat ub = Field51_as_Nat u % p := by
    --           rw [← Nat.mod_eq_of_lt hub_lt]; exact hub_mod
    --         have h_m_canon : U8x32_as_Nat mb = Field51_as_      -- have h_ONE_bounds : ∀ i < 5, one[i]!.val < 2 ^ 54 := by
      --   intro i hi
      --   interval_cases i
      --   sorry
      --   sorry
      --   sorry
      --   sorry
      --   sorry
      -- grind only
-- Nat MINUS_ONE % p := by
    --           rw [← Nat.mod_eq_of_lt hmb_lt]; exact hmb_mod
    --         rw [h_u_canon, h_m_canon, h4]

    --       have h_x_one : x = Choice.one := x_post.mpr h_eq_bytes
    --       have h_x_val : x.val = 1#u8 := by rw [h_x_one]; rfl
    --       absurd h_x_val
    --       assumption

    --     have h_fe2_inv := fe2_post_1 h_fe1_ne_zero
    --     have h_fe1_eq : Field51_as_Nat fe1 % p = (Field51_as_Nat u + 1) % p := by
    --       have h_ONE : Field51_as_Nat FieldElement51.ONE = 1 := FieldElement51.ONE_spec
    --       rw [h_expand, h_ONE]

    --     have h_fe_eq : Field51_as_Nat fe % p = (Field51_as_Nat u + p - 1) % p := by
    --       have h_ONE : Field51_as_Nat FieldElement51.ONE = 1 := FieldElement51.ONE_spec
    --       rw [h_ONE] at fe_post_2
    --       have key : (Field51_as_Nat fe + 1 + (p - 1)) % p = (Field51_as_Nat u + (p - 1)) % p := by
    --         rw [Nat.add_mod (Field51_as_Nat fe + 1), fe_post_2, ← Nat.add_mod]
    --       have hleft : (Field51_as_Nat fe + 1 + (p - 1)) % p = Field51_as_Nat fe % p := by
    --         have h : Field51_as_Nat fe + 1 + (p - 1) = Field51_as_Nat fe + p := by omega
    --         rw [h, Nat.add_mod, Nat.mod_self, add_zero]
    --         exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
    --       have hright : (Field51_as_Nat u + (p - 1)) % p = (Field51_as_Nat u + p - 1) % p := by
    --         grind only
    --       rw [← hleft, key]; exact hright

    --     have h_u_eq : Field51_as_Nat u % p = U8x32_as_Nat mp % 2^255 % p := by
    --       exact u_post_1

    --     calc Field51_as_Nat res_post_2.Y * Field51_as_Nat Z_inv * (U8x32_as_Nat mp % 2 ^ 255 + 1) % p

    --         = y_val * (U8x32_as_Nat mp % 2 ^ 255 + 1) % p := by
    --           simp only [Nat.mul_mod (Field51_as_Nat res_post_2.Y * Field51_as_Nat Z_inv), h_affine_y]
    --           simp [Nat.mul_mod]

    --         _ = (Field51_as_Nat fe * Field51_as_Nat fe2) * (U8x32_as_Nat mp % 2 ^ 255 + 1) % p := by
    --             have h :
    --               y_val % p = (Field51_as_Nat fe * Field51_as_Nat fe2) % p :=
    --               h_y_val_eq
    --             have :=
    --               congrArg (fun x => x * (U8x32_as_Nat mp % 2 ^ 255 + 1) % p) h

    --             simpa [Nat.mul_mod] using this

    --         _ = (Field51_as_Nat fe * Field51_as_Nat fe2) * (Field51_as_Nat u % p + 1) % p := by
    --             have h_mp : Field51_as_Nat u % p = U8x32_as_Nat mp % 2 ^ 255 % p := by
    --               exact h_u_eq
    --             simp [h_mp, Nat.mul_mod, Nat.add_mod]

    --         _ = (Field51_as_Nat fe * Field51_as_Nat fe2) * Field51_as_Nat fe1 % p := by

    --           have h1 : (Field51_as_Nat u % p + 1) % p =
    --           Field51_as_Nat fe1 % p := by
    --             have := Nat.add_mod (Field51_as_Nat u) 1 p
    --             simp at this
    --             simp [h_fe1_eq]

    --           have h2 :
    --           Field51_as_Nat fe * Field51_as_Nat fe2 *
    --               (Field51_as_Nat u % p + 1) % p
    --             =
    --           Field51_as_Nat fe * Field51_as_Nat fe2 *
    --               (Field51_as_Nat fe1 % p) % p := by
    --             simp [Nat.mul_mod]
    --             grind only
    --           rw [Nat.mul_mod]
    --           rw [h1]
    --           rw [← Nat.mul_mod]

    --         _ = Field51_as_Nat fe * (Field51_as_Nat fe2 * Field51_as_Nat fe1) % p := by
    --             ring_nf

    --         _ = Field51_as_Nat fe * 1 % p := by
    --           have h_mul : (Field51_as_Nat fe2 * Field51_as_Nat fe1) % p = 1 := by
    --             have := h_fe2_inv
    --             simpa [Nat.mul_mod] using this
    --           have : Field51_as_Nat fe * (Field51_as_Nat fe2 * Field51_as_Nat fe1) % p = Field51_as_Nat fe * 1 % p := by
    --             simp [Nat.mul_mod, h_mul]
    --           grind only
    --         _ = Field51_as_Nat fe % p := by
    --             ring_nf

    --         _ = (Field51_as_Nat u + p - 1) % p := h_fe_eq

    --         _ = (U8x32_as_Nat mp % 2^ 255 + p - 1) % p := by
    --           have hp1 : 1 ≤ p := by decide
    --           rw [Nat.add_sub_assoc hp1, Nat.add_sub_assoc hp1]
    --           rw [Nat.add_mod (Field51_as_Nat u), Nat.add_mod (U8x32_as_Nat mp % 2 ^ 255),
    --               Nat.mod_eq_of_lt (show p - 1 < p from by omega), h_u_eq]


end curve25519_dalek.montgomery.MontgomeryPoint
