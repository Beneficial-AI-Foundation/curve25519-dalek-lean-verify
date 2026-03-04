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

/-
natural language description:

    Converts a MontgomeryPoint (u-coordinate only) to an EdwardsPoint using the
    birational map y = (u-1)/(u+1) (mod p), where p = 2^255 - 19.
    Special case: when u ≡ -1 (mod p), returns None (point is on the twist).
    Otherwise, computes y, encodes it with the specified sign bit, and decompresses
    to obtain a full EdwardsPoint.

natural language specs:

    When the function returns Some(edwards_point):
      - The Edwards y-coordinate satisfies the birational map: y ≡ (u-1)/(u+1) (mod p)
      - The edwards_point lies on the twisted Edwards curve equation
      - The sign bit is properly encoded

    where p = 2^255 - 19
-/

-- /-- **Spec and proof concerning `montgomery.MontgomeryPoint.to_edwards`**:
-- - When the function returns Some(edwards_point), the Edwards y-coordinate satisfies
--   the birational map: y * (u + 1) ≡ (u - 1) (mod p)
-- - The returned point lies on the twisted Edwards curve
-- -/


set_option maxHeartbeats 1600000 in
@[progress]
theorem to_edwards_spec (mp : MontgomeryPoint) (sign : U8) :
      to_edwards mp sign ⦃ result =>
        (∀ ep, result = some ep →
          ∃ Z_inv,
            field.FieldElement51.invert ep.Z = ok Z_inv ∧
            let u := U8x32_as_Nat mp
            let y := Field51_as_Nat ep.Y * Field51_as_Nat Z_inv % p  -- Affine y = Y/Z
            (y * ((u + 1) % p)) % p = ((u - 1) % p) % p)
      ⦄ := by

  unfold to_edwards
  progress*
  -- After progress*, we have eliminated from_bytes
  -- Now need to handle: eq, sub, add, invert, mul, to_bytes, bit ops, decompress
  unfold FieldElement51.Insts.CoreCmpPartialEqFieldElement51.eq
  progress*  -- This eliminates ct_eq

  -- Add auxiliary lemmas for bounds on constants
  -- TODO: These can be proven by evaluating the constants
  have h_ONE_bounds : ∀ i < 5, FieldElement51.ONE[i]!.val < 2 ^ 53 := by
    intro i hi
    unfold FieldElement51.ONE
    interval_cases i <;> decide

  have h_MINUS_ONE_bounds : ∀ i < 5, FieldElement51.MINUS_ONE[i]!.val < 2 ^ 54 := by
    intro i hi
    unfold FieldElement51.MINUS_ONE
    interval_cases i <;> decide

  -- We also need bounds that are compatible with u
  have h_u_sub_bounds : ∀ i < 5, u[i]!.val < 2 ^ 63 := by
    intro i hi
    have := u_post_2 i hi
    omega

  have h_ONE_sub_bounds : ∀ i < 5, FieldElement51.ONE[i]!.val < 2 ^ 54 := by
    intro i hi
    have := h_ONE_bounds i hi
    omega

  have h_u_add_bounds : ∀ i < 5, u[i]!.val < 2 ^ 53 := by
    intro i hi
    have := u_post_2 i hi
    omega

  -- Now manually apply the specs with appropriate bounds
  -- First handle Choice.from - it's simple, just unfold
  unfold Bool.Insts.CoreConvertFromChoice.from
  simp
  -- Split on the if-then-else
  split
  · -- Case: b = true (u = MINUS_ONE, return none)
    simp
  · progress*
    · grind only
    · grind only
    · have h_res := res_post_1 res_post_2 res_post_3
      obtain ⟨Z_inv, x_val, y_val, x_is_neg, h_Zinv, h_X, h_Y, h_neg, h_curve, h_y_val, h_sign, h_T⟩ := h_res
  -- · -- Main proof at line 118
    -- Step 0: Provide the witness Z_inv and split the goal
      use Z_inv
      constructor
      · -- Prove: field.FieldElement51.invert res_post_2.Z = ok Z_inv
        exact h_Zinv
      -- Now prove the main equation
      -- Goal: Field51_as_Nat res_post_2.Y * Field51_as_Nat Z_inv * (U8x32_as_Nat mp + 1) % p
      --       = (U8x32_as_Nat mp - 1) % p
      ·
        -- Step 1: Substitute res_post_2.Y * Z_inv with y_val using h_Y
        have h_affine_y : Field51_as_Nat res_post_2.Y * Field51_as_Nat Z_inv % p = y_val := h_Y

        -- Step 2: Chain y_val back through y_bytes1, y_bytes, y, fe, fe2, to show it equals (u-1)/(u+1)

        -- Step 2a: Relate y_bytes1 to y_bytes (modifying sign bit doesn't affect low 255 bits)
        have h_bytes_equiv : U8x32_as_Nat y_bytes1 % 2^255 % p = U8x32_as_Nat y_bytes % 2^255 % p := by
          rw [y_bytes1_post]
          -- Goal: U8x32_as_Nat (y_bytes.set 31#usize i2) % 2^255 % p = U8x32_as_Nat y_bytes % 2^255 % p
          -- Need lemma about set preserving low bits
          sorry

        -- Step 2b: Simplify % 2^255 using the fact that y_bytes < p < 2^255
        have h_bytes_mod : U8x32_as_Nat y_bytes % 2^255 % p = U8x32_as_Nat y_bytes % p := by
          have hp : p < 2^255 := by
            unfold p
            norm_num
          have hlt : U8x32_as_Nat y_bytes < p := y_bytes_post_2
          -- If x < p < 2^255, then x % 2^255 = x, so x % 2^255 % p = x % p
          have h_lt_255 : U8x32_as_Nat y_bytes < 2^255 := by omega
          rw [Nat.mod_eq_of_lt h_lt_255]

        -- Step 2c: Connect y_bytes to field element y
        have h_y_bytes : U8x32_as_Nat y_bytes % p = Field51_as_Nat y % p := by
          -- From y_bytes_post_1 : U8x32_as_Nat y_bytes ≡ Field51_as_Nat y [MOD p]
          -- In Lean 4, ModEq unfolds to the equality we need
          exact y_bytes_post_1

        -- Step 2d: Connect y to fe * fe2
        have h_y_eq : Field51_as_Nat y % p = (Field51_as_Nat fe * Field51_as_Nat fe2) % p := by
          -- From y_post_1 : Field51_as_Nat y ≡ Field51_as_Nat fe * Field51_as_Nat fe2 [MOD p]
          -- In Lean 4, ModEq unfolds to the equality we need
          exact y_post_1

        -- Step 2e: Chain everything together to get y_val = (fe * fe2) % p
        have h_y_val_eq : y_val % p = (Field51_as_Nat fe * Field51_as_Nat fe2) % p := by
          calc y_val % p
              = U8x32_as_Nat y_bytes1 % 2^255 % p := h_y_val
            _ = U8x32_as_Nat y_bytes % 2^255 % p := h_bytes_equiv
            _ = U8x32_as_Nat y_bytes % p := h_bytes_mod
            _ = Field51_as_Nat y % p := h_y_bytes
            _ = (Field51_as_Nat fe * Field51_as_Nat fe2) % p := h_y_eq

        -- Step 3: Prove fe1 ≠ 0 (i.e., u ≠ -1 mod p)
        have h_fe1_ne_zero : Field51_as_Nat fe1 % p ≠ 0 := by
          -- We're in the else branch: ¬x.val = 1#u8
          -- From x_post: x = Choice.one ↔ u.to_bytes = FieldElement51.MINUS_ONE.to_bytes
          -- So u.to_bytes ≠ MINUS_ONE.to_bytes
          intro h_contra
          -- If fe1 % p = 0, then (u + 1) % p = 0, so u ≡ -1 (mod p)

          -- We need to show that fe1 % p = 0 implies u.to_bytes = MINUS_ONE.to_bytes
          -- This requires: if (u + 1) % p = 0, then u % p = p - 1 = MINUS_ONE % p
          -- and since to_bytes produces canonical representations, they should be equal

          -- We need a lemma about to_bytes being injective on canonical representatives
          -- For now, leave as sorry as this requires the full to_bytes_spec which isn't proven yet
          have h_eq_bytes : u.to_bytes = FieldElement51.MINUS_ONE.to_bytes := by sorry

          -- From h_eq_bytes and x_post, we get x = Choice.one
          have h_x_one : x = Choice.one := x_post.mpr h_eq_bytes

          -- But x = Choice.one means x.val = 1#u8, contradicting the else branch condition
          have h_x_val : x.val = 1#u8 := by rw [h_x_one]; rfl

          -- This contradicts the else branch condition ¬x.val = 1#u8
          -- Use absurd to derive False
          absurd h_x_val
          assumption

        -- Step 3a: Get the inversion property
        have h_fe2_inv := fe2_post_1 h_fe1_ne_zero
        -- h_fe2_inv : Field51_as_Nat fe2 % p * (Field51_as_Nat fe1 % p) % p = 1

        -- Step 4: Connect fe1 to u + 1
        have h_fe1_eq : Field51_as_Nat fe1 % p = (Field51_as_Nat u + 1) % p := by
          -- From fe1_post_1: ∀ i < 5, ↑fe1[i]! = ↑u[i]! + ↑FieldElement51.ONE[i]!
          -- This means fe1 is the limb-wise sum of u and ONE
          -- Need to show this equals Field51_as_Nat u + Field51_as_Nat ONE mod p
          have h_ONE : Field51_as_Nat FieldElement51.ONE = 1 := FieldElement51.ONE_spec

          -- Expand Field51_as_Nat and use linearity of sum
          have h_expand : Field51_as_Nat fe1 = Field51_as_Nat u + Field51_as_Nat FieldElement51.ONE := by
            unfold Field51_as_Nat
            -- Goal: ∑ i, 2^(51*i) * fe1[i].val = ∑ i, 2^(51*i) * u[i].val + ∑ i, 2^(51*i) * ONE[i].val
            rw [← Finset.sum_add_distrib]
            -- Now show the functions agree pointwise
            apply Finset.sum_congr rfl
            intro i hi
            -- Use fe1_post_1: fe1[i].val = u[i].val + ONE[i].val
            have h_limb := fe1_post_1 i (Finset.mem_range.mp hi)
            simp only at h_limb
            rw [h_limb]
            ring

          rw [h_expand, h_ONE]

        -- Step 5: Connect fe to u - 1
        have h_fe_eq : Field51_as_Nat fe % p = (Field51_as_Nat u - 1) % p := by
          -- From fe_post_2: (Field51_as_Nat fe + Field51_as_Nat FieldElement51.ONE) % p = Field51_as_Nat u % p
          have h_ONE : Field51_as_Nat FieldElement51.ONE = 1 := FieldElement51.ONE_spec
          rw [h_ONE] at fe_post_2
          -- fe_post_2 : (Field51_as_Nat fe + 1) % p = Field51_as_Nat u % p

          -- Use modular arithmetic: (a + 1) % p = b % p implies a % p = (b - 1) % p
          -- This is a standard property that requires careful handling of natural number subtraction

          -- The key insight: we want to show that fe ≡ u - 1 (mod p)
          -- We have: fe + 1 ≡ u (mod p)
          -- In the integers/field, this clearly gives fe ≡ u - 1
          -- But in natural numbers with % we need to be careful

          sorry

        -- Step 6: Connect u to mp
        have h_u_eq : Field51_as_Nat u % p = U8x32_as_Nat mp % 2^255 % p := by
          -- From u_post_1 : Field51_as_Nat u ≡ U8x32_as_Nat mp % 2^255 [MOD p]
          -- In Lean 4, ModEq unfolds to the equality we need
          exact u_post_1

        have h_u_mod : U8x32_as_Nat mp % 2^255 % p = U8x32_as_Nat mp % p := by
          -- mp is a MontgomeryPoint, which is Array U8 32
          -- U8x32_as_Nat mp < 2^256, but we need < 2^255 for this to work
          -- Actually, from_bytes masks to 2^255, so Field51_as_Nat u corresponds to mp % 2^255
          sorry

        -- Step 7: Main calculation
        calc Field51_as_Nat res_post_2.Y * Field51_as_Nat Z_inv * (U8x32_as_Nat mp + 1) % p

            -- Use h_Y to replace res_post_2.Y * Z_inv with y_val
            = y_val * (U8x32_as_Nat mp + 1) % p := by
                -- -- Apply Nat.mul_mod to decompose the modulo
                -- rw [Nat.mul_mod]
                -- -- Now rewrite using h_affine_y
                -- rw [h_affine_y]
                -- rw [Nat.mul_mod]
                -- have (U8x32_as_Nat mp + 1) % p % p = (U8x32_as_Nat mp + 1) % p by :=
                --   sorry
                sorry

            -- Use h_y_val_eq to replace y_val with (fe * fe2)
            _ = (Field51_as_Nat fe * Field51_as_Nat fe2) * (U8x32_as_Nat mp + 1) % p := by
                -- conv_lhs => arg 1; rw [← Nat.mod_eq_of_lt (by sorry : y_val < p)]
                -- rw [h_y_val_eq]
                -- ring_nf
                sorry
            -- Relate mp to u
            _ = (Field51_as_Nat fe * Field51_as_Nat fe2) * (Field51_as_Nat u % p + 1) % p := by
                -- congr 1
                -- rw [← h_u_eq, ← h_u_mod]
                sorry

            -- Substitute u + 1 with fe1
            _ = (Field51_as_Nat fe * Field51_as_Nat fe2) * Field51_as_Nat fe1 % p := by
                -- congr 1
                -- rw [← h_fe1_eq]
                sorry

            -- Rearrange: fe * fe2 * fe1 = fe * (fe2 * fe1)
            _ = Field51_as_Nat fe * (Field51_as_Nat fe2 * Field51_as_Nat fe1) % p := by
                ring_nf

            -- Use fe2 * fe1 = 1
            _ = Field51_as_Nat fe * 1 % p := by
              sorry

            -- Simplify
            _ = Field51_as_Nat fe % p := by
                ring_nf

            -- Use fe = u - 1
            _ = (Field51_as_Nat u - 1) % p := h_fe_eq

            -- Relate u to mp
            _ = (U8x32_as_Nat mp % p - 1) % p := by
                -- First establish that Field51_as_Nat u % p = U8x32_as_Nat mp % p
                have h_u_mp : Field51_as_Nat u % p = U8x32_as_Nat mp % p := by
                  sorry
                -- Rewrite using the fact that (a - 1) % p depends on a % p
                -- conv_lhs => arg 1; rw [Nat.sub_mod, h_u_mp]
                -- rw [← Nat.sub_mod]
                sorry
            -- Simplify
            _ = (U8x32_as_Nat mp - 1) % p := by
                sorry


end curve25519_dalek.montgomery.MontgomeryPoint
