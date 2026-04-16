/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Specs.Field.FieldElement51.IsNegative

/-! # Spec Theorem for `AffinePoint::compress`

Specification and proof for `edwards.affine.AffinePoint.compress`.

This function converts an Edwards affine point (x, y) into its 32-byte
CompressedEdwardsY representation by serializing y in little-endian and
storing the sign bit of x in the most significant bit of the last byte.

**Source**: curve25519-dalek/src/edwards/affine.rs

## TODO
- Complete proof
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.math
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.edwards.affine.AffinePoint

/-
Natural language description:

    * Takes an affine Edwards point with coordinates (x, y)
    * Serializes y to a 32-byte little-endian array
    * Computes the sign (parity) bit of x as a subtle.Choice
    * Sets the MSB (bit 7) of byte 31 of the serialized y to this sign bit (via XOR)
    * Returns the resulting 32-byte array as CompressedEdwardsY

Natural language specs:

    * The function always succeeds (no panic) when the AffinePoint is valid
    * On success, the byte encoding equals compress_edwards_pure(self.toPoint),
      i.e. the canonical y-coordinate in the lower 255 bits with the x parity
      in bit 255
-/

set_option maxHeartbeats 600000 in -- heavy step
/-- **Spec and proof concerning `edwards.affine.AffinePoint.compress`**:
- Requires: the AffinePoint is valid (limbs < 2^54, on curve)
- Ensures: the compressed bytes equal the pure mathematical compression of the point
-/
@[externally_verified, step] -- proven in Verus
theorem compress_spec (self : AffinePoint) (hself : self.IsValid) :
    compress self ⦃ result =>
    U8x32_as_Nat result = compress_edwards_pure (self.toPoint) ⦄ := by
  unfold compress
  -- Chain to_bytes_spec (y → canonical bytes) and is_negative_spec (x → sign)
  let* ⟨s, h_mod, h_lt⟩ ← to_bytes_spec
  let* ⟨ c, c_post ⟩ ← field.FieldElement51.is_negative_spec
  -- Reduce unwrap_u8 (definitional: ok c.val)
  unfold subtle.Choice.unwrap_u8
  simp only [step_simps]
  -- Key bridges
  have h_toPoint : self.toPoint = ⟨self.x.toField, self.y.toField, hself.on_curve⟩ := by
    unfold AffinePoint.toPoint; rw [dif_pos hself]
  have h_s_eq : U8x32_as_Nat s = Field51_as_Nat self.y % p := by
    rw [Nat.ModEq] at h_mod; rw [Nat.mod_eq_of_lt h_lt] at h_mod; agrind
  have h_lt_255 : U8x32_as_Nat s < 2 ^ 255 :=
    Nat.lt_trans h_lt (by unfold p; decide)
  have h_b31_lt : s.val[31]!.val < 128 := by
    have := high_bit_zero_of_lt_255 s h_lt_255; omega
  -- Case split on c.val (0 or 1) before stepping remaining ops
  rcases c.valid with hc | hc <;> simp only [hc, step_simps]
  · -- c.val = 0: 0 <<< 7 = 0, XOR identity, result ≈ s
    let* ⟨ i1, i1_post1, i1_post2 ⟩ ← U8.ShiftLeft_IScalar_spec
    let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
    let* ⟨ i3, i3_post1, i3_post2 ⟩ ← UScalar.xor_spec
    let* ⟨ s1, s1_post ⟩ ← Array.update_spec
    rw [compress_edwards_pure, h_toPoint]; simp only
    have : ¬((Field51_as_Nat self.x % p) % 2 = 1) := by
      intro h; exact absurd (c_post.mpr h) (by simp [hc])
    have h_neg_false : is_negative self.x.toField = false := by
      unfold is_negative toField
      simp only [ZMod.val_natCast]; agrind
    rw [h_neg_false]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.reducePow, zero_mul, add_zero]
    -- i3 = i2 (XOR with 0 is identity): i1.val = 0 so (i2 ^^^ i1).val = i2.val
    have hi3_eq : i3 = i2 := by
      apply UScalar.eq_of_val_eq
      have h1 : (i2 ^^^ i1).val = i2.val := by
        have hi1_zero : i1.val = 0 := by simp [i1_post1]
        have : i1 = 0#u8 := UScalar.eq_of_val_eq hi1_zero
        rw [this]; simp
      rw [i3_post1]; exact h1
    -- s1 = s (set byte 31 to itself is no-op)
    have hs1_eq : s1 = s := by
      rw [s1_post, hi3_eq, i2_post]
      apply Subtype.ext
      simp only [Array.set_val_eq]
      have h31 : (↑(31#usize) : ℕ) = 31 := by decide
      rw [h31]; apply List.ext_getElem (by simp [s.property])
      intro i hi1 _; by_cases h : i = 31
      · subst h; simp [s.property]
      · grind
    rw [hs1_eq]
    simp only [toField, ZMod.val_natCast]; exact h_s_eq
  · -- c.val = 1: 1 <<< 7 = 128, XOR sets bit 7 of byte 31
    let* ⟨ i1, i1_post1, i1_post2 ⟩ ← U8.ShiftLeft_IScalar_spec
    let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
    let* ⟨ i3, i3_post1, i3_post2 ⟩ ← UScalar.xor_spec
    let* ⟨ s1, s1_post ⟩ ← Array.update_spec
    rw [compress_edwards_pure, h_toPoint]; simp only
    have h_neg_true : is_negative self.x.toField = true := by
      unfold is_negative toField
      simp only [ZMod.val_natCast, beq_iff_eq]
      agrind
    rw [h_neg_true]
    simp only [toField, ZMod.val_natCast, ↓reduceIte, one_mul]
    -- Reduce to: U8x32_as_Nat s1 = U8x32_as_Nat s + 2^255
    rw [← h_s_eq]
    -- i3.val = i2.val + 128 (XOR with 128 when bit 7 is 0)
    have h_i1_val : i1.val = 128 := by rw [i1_post1]; scalar_tac
    have h_i3_val : i3.val = i2.val + 128 := by
      have h_lt' : i2.val < 128 := by rw [i2_post]; exact h_b31_lt
      have h_i1_eq : i1 = 128#u8 := UScalar.eq_of_val_eq h_i1_val
      rw [i3_post1, h_i1_eq]
      simp only [UScalar.val_xor, UScalar.ofNatCore_val_eq]
      sorry
    -- Sum decomposition of U8x32_as_Nat s (split off byte 31)
    have h_orig : U8x32_as_Nat s =
        (∑ j ∈ Finset.range 31, 2^(8*j) * (s.val[j]!).val) + 2^248 * (↑s)[31]!.val := by
      unfold U8x32_as_Nat
      rw [Finset.sum_range_succ, show (8:Nat) * 31 = 248 from by norm_num]
      simp [Array.getElem!_Nat_eq]
    -- Sum decomposition of U8x32_as_Nat (s.set 31 i3) (adapted from ToEdwards.lean)
    have h_set : U8x32_as_Nat (s.set 31#usize i3) =
        (∑ j ∈ Finset.range 31, 2^(8*j) * (s.val[j]!).val) + 2^248 * i3.val := by
      unfold U8x32_as_Nat
      rw [Finset.sum_range_succ, show (8:Nat) * 31 = 248 from by norm_num]
      simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
      have h_idx : (↑(31#usize) : ℕ) = 31 := by decide
      rw [h_idx, congrArg UScalar.val (List.getElem!_set (↑s : List U8) 31 i3
        (by simp [s.property]))]
      have h_eq : ∑ j ∈ Finset.range 31, 2^(8*j) *
              UScalar.val ((↑s : List U8).set 31 i3)[j]! =
          ∑ j ∈ Finset.range 31, 2^(8*j) *
              UScalar.val (↑s : List U8)[j]! :=
        Finset.sum_congr rfl (fun j hj => congrArg (2^(8*j) * ·)
          (congrArg UScalar.val (List.getElem!_set_ne (↑s : List U8) 31 j i3
            (Or.inr (Or.inr (Or.inr (Finset.mem_range.mp hj)))))))
      grind only
    -- Combine: s.set 31 i3 adds 2^248 * 128 = 2^255 to U8x32_as_Nat s
    rw [s1_post, h_set, h_i3_val, i2_post, h_orig];
    agrind

end curve25519_dalek.edwards.affine.AffinePoint
