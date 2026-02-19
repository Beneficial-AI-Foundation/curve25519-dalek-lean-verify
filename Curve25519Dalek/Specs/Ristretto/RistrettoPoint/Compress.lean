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
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.SQRT_M1
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.INVSQRT_A_MINUS_D

/-! # Spec Theorem for `RistrettoPoint::compress`

Specification and proof for `RistrettoPoint::compress`.

This function implements the Ristretto compression (ENCODE) function, which maps a
RistrettoPoint to its canonical 32-byte representation. The function is defined in the

- [Ristretto specification](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-08#section-4.3.2).

It takes a RistrettoPoint (which represents an equivalence class of Edwards points) and produces a unique, canonical byte representation.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas.Std Result
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

/-- **Auxiliary technical lemma for `conditional_negate` on FieldElement51**:
Conditionally negates a field element modulo p based on choice (1 = negate, 0 = unchanged),
preserving 54-bit limb bounds.
-/
@[progress]
lemma conditional_negate_FieldElement51_spec
    (self : backend.serial.u64.field.FieldElement51)
    (choice : subtle.Choice)
    (h_bounds : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    ∃ res,
      subtle.ConditionallyNegatable.Blanket.conditional_negate
        subtle.ConditionallySelectableFieldElement51
        core.ops.arith.NegShared0FieldElement51FieldElement51 self choice = ok res ∧
      (if choice.val = 1#u8 then
        (Field51_as_Nat res + Field51_as_Nat self) % p = 0
       else
        Field51_as_Nat res = Field51_as_Nat self) ∧
      (∀ i < 5, res[i]!.val < 2 ^ 54) := by
  unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
  obtain ⟨self_neg, hneg_call, hneg_sem, hneg_bounds⟩ :=
    backend.serial.u64.field.NegShared0FieldElement51FieldElement51.neg_spec self h_bounds
  simp only [hneg_call, bind_tc_ok]
  obtain ⟨res, hsel_call, hsel_limbs⟩ :=
    backend.serial.u64.field.ConditionallySelectableFieldElement51.conditional_select_spec
      self self_neg choice
  use res, hsel_call
  constructor
  · split_ifs with h
    · have : Field51_as_Nat res = Field51_as_Nat self_neg := by
        unfold Field51_as_Nat
        exact Finset.sum_congr rfl fun i hi => by simp [hsel_limbs i (Finset.mem_range.mp hi), h]
      rw [this, Nat.add_comm, hneg_sem]
    · unfold Field51_as_Nat
      exact Finset.sum_congr rfl fun i hi => by simp [hsel_limbs i (Finset.mem_range.mp hi), h]
  · intro i hi
    simp [hsel_limbs i hi]
    split_ifs
    · exact Nat.lt_of_le_of_lt (hneg_bounds i hi) (by norm_num : 2^51 + (2^13 - 1) * 19 < 2^54)
    · exact h_bounds i hi







/-- **Spec and proof concerning `ristretto.RistrettoPoint.compress`**:
• The function always succeeds (no panic) for all valid RistrettoPoint inputs
• The output is a valid CompressedRistretto 32-byte representation
• The output accurately reflects the output of the pure mathematical compression function
-/
@[progress]
theorem compress_spec (rist : RistrettoPoint) (h_rist_valid : rist.IsValid) :
    ∃ result, compress rist = ok result ∧
    result.IsValid ∧
    math.compress_pure rist.toPoint = U8x32_as_Nat result := by


  unfold compress

  progress*


  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · sorry

  · constructor

    · sorry

    · sorry


end curve25519_dalek.ristretto.RistrettoPoint
