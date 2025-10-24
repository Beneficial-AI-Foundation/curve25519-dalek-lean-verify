/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs
import Curve25519Dalek.Proofs.Aux
import Curve25519Dalek.Proofs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Curve25519Dalek.Proofs.Tactics


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
theorem decompose_or_limbs (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 48 ||| limb1.val <<< 4 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 48 % 2 ^ 8) +
  ((limb1.val <<< 4) % 2 ^ 8) := by
  bvify 64 at *
  -- The idea is to do something similar to the proof above

  sorry

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
    U8x32_as_Nat result ≡ U64x5_as_Nat self [MOD p] ∧
    U8x32_as_Nat result < p := by
  unfold to_bytes
  progress*
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  refine ⟨?_, ?_⟩
  · sorry
  · sorry

end curve25519_dalek.backend.serial.u64.field.FieldElement51
