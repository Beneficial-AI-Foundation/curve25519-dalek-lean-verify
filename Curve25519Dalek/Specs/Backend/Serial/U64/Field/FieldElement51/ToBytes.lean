/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Curve25519Dalek.Tactics
import Curve25519Dalek.mvcgen
import Std.Do
import Std.Tactic.Do
set_option mvcgen.warning false
open Std.Do


/-! # to_bytes

Specification and proof for `FieldElement51::to_bytes`.

Much of the proof and aux lemmas contributed by Son Ho.

This function converts a field element to its canonical 32-byte little-endian representation.
It performs reduction modulo 2^255-19 and encodes the result as bytes.

Source: curve25519-dalek/src/backend/serial/u64/field.rs

## TODO
- Complete proof
-/

set_option linter.style.setOption false
set_option maxHeartbeats 2000000

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

-- TODO: generalize and add to the standard library
@[local simp]
theorem U64_cast_U8 (x : U64) : (UScalar.cast UScalarTy.U8 x).val = x.val % 2^8 := by
  simp only [UScalar.cast, UScalarTy.U64_numBits_eq, UScalarTy.U8_numBits_eq,
    Aeneas.Bvify.U64.UScalar_bv, BitVec.truncate_eq_setWidth]
  simp only [UScalar.val]
  simp only [UScalarTy.U8_numBits_eq, BitVec.toNat_setWidth, UScalar.bv_toNat,
    UScalarTy.U64_numBits_eq, Aeneas.Bvify.U64.UScalar_bv]

-- This is specific to the problem below
theorem recompose_decomposed_limb (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val =
  limb.val % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 8 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 16 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 24 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 32 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 40 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 48 % 2 ^ 8)
  := by
  bvify 64 at *
  bv_decide


-- TODO: move to standard library
attribute [simp_scalar_simps] BitVec.toNat_shiftLeft


-- We also need something like this
theorem recompose_decomposed_limb_split (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 4 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 4 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 12 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 20 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 28 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 36 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 44 % 2 ^ 8) =
  2 ^ 4 * limb.val
  := by
  bvify 64 at *
  /- Small trick when bvify doesn't work: we can prove the property we
     want about bit-vectors, then convert it back to natural numbers with
     `natify` and `simp_scalar`. In particular, `simp_scalar` is good at simplifying
     things like `x % 2 ^ 32` when `x < 2^32`, etc. -/
  have : BitVec.ofNat 64 (limb.val <<< 4) = limb.bv <<< 4 := by
    natify
    simp_scalar
  simp [this]
  bv_decide


-- This is specific to the problem below
-- The key insight is that limb0 >>> 48 has at most 3 bits (since limb0 < 2^51),
-- so it doesn't overlap with limb1 <<< 4 in the lower 8 bits.
-- After shifting right by 48, we get at most bits 0-2 set (since original has bits 0-50).
-- limb1 <<< 4 % 2^8 gives bits 4-7 in the lower byte.
-- Since bits 0-2 and bits 4-7 don't overlap, OR equals addition.
theorem decompose_or_limbs (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 48 ||| limb1.val <<< 4 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 48 % 2 ^ 8) +
  ((limb1.val <<< 4) % 2 ^ 8) := by
  -- Key bounds
  have hshift : limb0.val >>> 48 < 8 := by
    simp only [Nat.shiftRight_eq_div_pow]
    omega
  have hshift' : limb0.val >>> 48 < 256 := by omega
  -- The left shift mod 2^8 is divisible by 16
  have hleft_div : (limb1.val <<< 4) % 256 % 16 = 0 := by
    simp only [Nat.shiftLeft_eq]
    omega
  -- Use bitvector reasoning for the OR/AND relationship
  -- First, show that the shift mod U64.size equals the regular shift for values < 2^60
  have hmod_eq : limb1.val <<< 4 % U64.size = limb1.val <<< 4 % 2^64 := sorry
  -- The key insight: when a < 8 and b % 16 = 0, we have (a ||| b) % 256 = a + b % 256
  -- because a uses only bits 0-2 and b % 256 uses only bits 4-7
  -- For the right side simplification
  have h_rhs_eq : limb0.val >>> 48 % 2^8 = limb0.val >>> 48 := Nat.mod_eq_of_lt hshift'
  -- For the left side, we work with bitvectors
  -- Convert to 8-bit bitvector equality and use bv_decide
  suffices h : ((limb0.bv >>> 48).toNat ||| (limb1.bv <<< 4).toNat % U64.size) % 256 =
               (limb0.bv >>> 48).toNat + (limb1.bv <<< 4).toNat % 256 by
    simp only [UScalar.val, UScalar.bv_toNat] at h
    convert h using 2 <;> simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  -- Now use native decidability on concrete bitvector operations
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  -- The goal involves natural numbers with specific bounds
  -- limb0.bv.toNat >>> 48 < 8 (since limb0 < 2^51)
  -- (limb1.bv.toNat <<< 4) % 2^64 % 256 is divisible by 16
  have h1 : limb0.bv.toNat >>> 48 < 8 := by
    simp only [UScalar.bv_toNat]
    exact hshift
  have h2 : limb0.bv.toNat >>> 48 < 256 := by omega
  have h3 : (limb1.bv.toNat <<< 4 % U64.size) % 256 % 16 = 0 := by
    simp only [UScalar.bv_toNat, Nat.shiftLeft_eq]
    omega
  have h4 : (limb1.bv.toNat <<< 4 % U64.size) % 256 ≤ 240 := by
    have : (limb1.bv.toNat <<< 4 % U64.size) % 256 = (limb1.bv.toNat % 16) * 16 := by
      simp only [Nat.shiftLeft_eq]
      omega
    omega
  -- When a < 8 and b % 16 = 0 and b ≤ 240, then a ||| b = a + b (no overlap)
  have hor_add : limb0.bv.toNat >>> 48 ||| (limb1.bv.toNat <<< 4 % U64.size) % 256 =
                 limb0.bv.toNat >>> 48 + (limb1.bv.toNat <<< 4 % U64.size) % 256 := by
    have ha : limb0.bv.toNat >>> 48 < 8 := h1
    have hb : (limb1.bv.toNat <<< 4 % U64.size) % 256 % 16 = 0 := h3
    -- a uses bits 0-2, b uses bits 4-7, so no overlap
    have hand : limb0.bv.toNat >>> 48 &&& ((limb1.bv.toNat <<< 4 % U64.size) % 256) = 0 := by
      -- a < 8 means a ∈ {0,1,2,3,4,5,6,7} (bits 0,1,2)
      -- b % 16 = 0 means b has bits 0,1,2,3 clear
      -- Therefore a &&& b = 0
      have hb_low : (limb1.bv.toNat <<< 4 % U64.size) % 256 % 8 = 0 := by omega
      omega
    exact Nat.or_eq_add_of_and_eq_zero hand
  rw [hor_add]
  -- Now (a + b) % 256 = a + b when a + b < 256
  have hsum : limb0.bv.toNat >>> 48 + (limb1.bv.toNat <<< 4 % U64.size) % 256 < 256 := by
    omega
  rw [Nat.mod_eq_of_lt hsum, Nat.mod_eq_of_lt h2]

/-! ## Spec for `to_bytes` -/


/-- Byte-by-byte specification for `to_bytes` -/
theorem to_bytes_spec' (limbs : Array U64 5#usize) :
    ∃ result, to_bytes limbs = ok result ∧
    ∀ (i : Fin 32), result.val[i.val].val = match i.val with
      | 0  => limbs.val[0].val >>> 0 % 2^8
      | 1  => limbs.val[0].val >>> 8 % 2^8
      | 2  => limbs.val[0].val >>> 16 % 2^8
      | 3  => limbs.val[0].val >>> 24 % 2^8
      | 4  => limbs.val[0].val >>> 32 % 2^8
      | 5  => limbs.val[0].val >>> 40 % 2^8
      | 6  => (limbs.val[0].val >>> 48 ||| limbs.val[1].val <<< 4) % 2^8
      | 7  => limbs.val[1].val >>> 4 % 2^8
      | 8  => limbs.val[1].val >>> 12 % 2^8
      | 9  => limbs.val[1].val >>> 20 % 2^8
      | 10 => limbs.val[1].val >>> 28 % 2^8
      | 11 => limbs.val[1].val >>> 36 % 2^8
      | 12 => limbs.val[1].val >>> 44 % 2^8
      | 13 => limbs.val[2].val >>> 0 % 2^8
      | 14 => limbs.val[2].val >>> 8 % 2^8
      | 15 => limbs.val[2].val >>> 16 % 2^8
      | 16 => limbs.val[2].val >>> 24 % 2^8
      | 17 => limbs.val[2].val >>> 32 % 2^8
      | 18 => limbs.val[2].val >>> 40 % 2^8
      | 19 => (limbs.val[2].val >>> 48 ||| limbs.val[3].val <<< 4) % 2^8
      | 20 => limbs.val[3].val >>> 4 % 2^8
      | 21 => limbs.val[3].val >>> 12 % 2^8
      | 22 => limbs.val[3].val >>> 20 % 2^8
      | 23 => limbs.val[3].val >>> 28 % 2^8
      | 24 => limbs.val[3].val >>> 36 % 2^8
      | 25 => limbs.val[3].val >>> 44 % 2^8
      | 26 => limbs.val[4].val >>> 0 % 2^8
      | 27 => limbs.val[4].val >>> 8 % 2^8
      | 28 => limbs.val[4].val >>> 16 % 2^8
      | 29 => limbs.val[4].val >>> 24 % 2^8
      | 30 => limbs.val[4].val >>> 32 % 2^8
      | 31 => limbs.val[4].val >>> 40 % 2^8
      | _  => 0
    := by
  unfold to_bytes
  sorry


/-- **Spec for `backend.serial.u64.field.FieldElement51.to_bytes`**:

This function converts a field element to its canonical 32-byte little-endian representation.
The implementation performs reduction modulo p = 2^255-19 to ensure the result is in
canonical form.

The algorithm:
1. Reduces the field element using `reduce` to ensure all limbs are within bounds
2. Performs a final conditional reduction to ensure the result is < p
3. Packs the 5 limbs (each 51 bits) into 32 bytes in little-endian format

Specification:
- The function succeeds (no panic)
- The natural number interpretation of the byte array is congruent to the field element value modulo p
- The byte array represents the unique canonical form (0 ≤ value < p)
-/
@[progress]
theorem to_bytes_spec (self : backend.serial.u64.field.FieldElement51) :
    ∃ result, to_bytes self = ok result ∧
    U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] ∧
    U8x32_as_Nat result < p := by
  unfold to_bytes
  progress*
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  all_goals try simp [*] at *; scalar_tac
  refine ⟨?_, ?_⟩
  -- Modular congruence: U8x32_as_Nat s32 ≡ Field51_as_Nat self [MOD p]
  · sorry
  -- Bound: U8x32_as_Nat s32 < p
  · sorry

/-! ## mvcgen-based spec theorems

The `@[spec]` attribute tells `mvcgen` to use these theorems when it encounters
calls to `to_bytes`. These follow the pattern from Negate.lean.
-/

/-- Spec for to_bytes in Triple form, suitable for mvcgen.
    Tagged with @[spec] so mvcgen can use it for calls to to_bytes.

    This follows the pattern from Std.Do.Triple.SpecLemmas:
    - The postcondition is the generic Q passed in
    - The precondition captures the specification properties -/
@[spec]
theorem to_bytes_spec_triple (self : FieldElement51) (Q : PostCond (Array U8 32#usize) Aeneas.Std.ResultPostShape) :
    ⦃⌜∀ result, U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] →
              U8x32_as_Nat result < p →
              (Q.1 result).down⌝⦄
    to_bytes self
    ⦃Q⦄ := by
  -- Direct proof - we inline the properties needed
  unfold Triple
  intro h_Q
  -- First, establish that to_bytes succeeds with some result
  -- by unfolding and using progress on each step
  have h_exists : ∃ result, to_bytes self = ok result ∧
      U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] ∧
      U8x32_as_Nat result < p := by
    unfold to_bytes
    progress*
    · expand fe_post_1 with 5; scalar_tac
    · expand fe_post_1 with 5; scalar_tac
    · expand fe_post_1 with 5; scalar_tac
    · expand fe_post_1 with 5; scalar_tac
    · expand fe_post_1 with 5; scalar_tac
    · expand fe_post_1 with 5; scalar_tac
    all_goals try simp [*] at *; scalar_tac
    refine ⟨?_, ?_⟩
    -- Modular congruence
    · sorry
    -- Bound
    · sorry
  obtain ⟨result, h_ok, h_mod, h_bound⟩ := h_exists
  simp only [WP.wp, h_ok, Aeneas.Std.Result.wp_apply_ok]
  exact h_Q result h_mod h_bound

/-- User-friendly mvcgen spec with modular arithmetic and canonicity postconditions. -/
@[spec]
theorem to_bytes_spec_mvcgen (self : FieldElement51) :
    ⦃⌜True⌝⦄
    to_bytes self
    ⦃⇓ result => ⌜U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] ∧ U8x32_as_Nat result < p⌝⦄ := by
  -- Use the to_bytes_spec result directly
  obtain ⟨result, h_ok, h_mod, h_bound⟩ := to_bytes_spec self
  unfold Triple
  intro _htrue
  simp only [WP.wp, h_ok, Aeneas.Std.Result.wp_apply_ok, PostCond.noThrow, ExceptConds.false]
  exact ⟨h_mod, h_bound⟩

/-- Example: using mvcgen on a function that calls to_bytes.
    This demonstrates how mvcgen can use the @[spec] lemma. -/
example (fe : FieldElement51) :
    ⦃⌜True⌝⦄
    do let bytes ← to_bytes fe; pure bytes
    ⦃⇓ result => ⌜U8x32_as_Nat result ≡ Field51_as_Nat fe [MOD p]⌝⦄ := by
  -- mvcgen uses @[spec] to_bytes_spec_triple to handle the to_bytes call
  mvcgen
  -- VC after mvcgen: continuation condition
  intro result h_mod _h_bound
  -- Goal: wp⟦pure result⟧ Q
  simp only [WP.pure, PostCond.noThrow, ExceptConds.false]
  exact h_mod

end curve25519_dalek.backend.serial.u64.field.FieldElement51
