/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square2
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub

/-! # Spec Theorem for `ProjectivePoint::double`

Specification and proof for `ProjectivePoint::double`.

This function implements point doubling on the Curve25519 elliptic curve using projective
coordinates. Given a point P = (X:Y:Z), it computes 2P (the point added to itself via
elliptic curve addition).

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs
-/

open Aeneas.Std Result

open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.u64.field.FieldElement51.Add
open curve25519_dalek.backend.serial.u64.field.FieldElement51.Sub

namespace curve25519_dalek.backend.serial.curve_models.ProjectivePoint

/-
natural language description:

• Takes a ProjectivePoint with coordinates (X, Y, Z) and returns a CompletedPoint that results
from adding the input point to itself via elliptic curve point addition. Arithmetics are
performed in the field 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Given input point (X, Y, Z), the output CompletedPoint (X', Y', Z', T') satisfies:
- X' ≡ 2XY (mod p)
- Y' ≡ Y² + X² (mod p)
- Z' ≡ Y² - X² (mod p)
- T' ≡ 2Z² - Y² + X² (mod p)
-/

/-- **Spec and proof concerning `backend.serial.curve_models.ProjectivePoint.double`**:
- No panic (always returns successfully)
- Given input ProjectivePoint with coordinates (X, Y, Z), the output CompletedPoint (X', Y', Z', T')
satisfies the point doubling formulas modulo p:
- X' ≡ 2XY (mod p)
- Y' ≡ Y² + X² (mod p)
- Z' ≡ Y² - X² (mod p)
- T' ≡ 2Z² - Y² + X² (mod p)
where p = 2^255 - 19
These formulas implement Edwards curve point doubling, computing P + P
(elliptic curve point addition) where P = (X:Y:Z).
-/
@[progress]
theorem double_spec (q : ProjectivePoint) :
∃ c,
double q = ok c ∧
let X := Field51_as_Nat q.X
let Y := Field51_as_Nat q.Y
let Z := Field51_as_Nat q.Z
let X' := Field51_as_Nat c.X
let Y' := Field51_as_Nat c.Y
let Z' := Field51_as_Nat c.Z
let T' := Field51_as_Nat c.T
X' % p = (2 * X * Y) % p ∧
Y' % p = (Y^2 + X^2) % p ∧
Z' % p = (Y^2 - X^2) % p ∧
T' % p = (2 * Z^2 - Y^2 + X^2) % p
:= by
  unfold double

  progress*


  · -- Goal 1: Precondition for `add q.X q.Y`
    sorry
  · -- Goal 2: Precondition for `square X_plus_Y`
    sorry
  · -- Goal 3: Precondition for `add YY XX`
    sorry
  · -- Goal 4: Precondition for `sub YY XX`
    sorry
  · -- Goal 5: Precondition for `sub X_plus_Y_sq YY_plus_XX`
    sorry
  · -- Goal 6: Precondition for `sub ZZ2 YY_minus_XX`
    sorry
  · -- Goal 7: Precondition for `square q.X` (from 'let XX')
    -- (Note: The order of goals might differ slightly)
    sorry
  · -- Goal 8: Precondition for `square q.Y` (from 'let YY')
    sorry

  -- Goal 9:
  constructor

  · -- Goal 9.1: X' coordinate
    unfold Field51_as_Nat at *;

    have h_X_plus_Y : (∑ i ∈ Finset.range 5, 2^(51 * i) * (X_plus_Y[i]!).val) =
                      (∑ i ∈ Finset.range 5, 2^(51 * i) * (q.X[i]!).val) +
                      (∑ i ∈ Finset.range 5, 2^(51 * i) * (q.Y[i]!).val) := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
      intro i hi
      rw [X_plus_Y_post, Nat.mul_add]; exact Finset.mem_range.mp hi

    have h_YY_plus_XX : (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY_plus_XX[i]!).val) =
                        (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY[i]!).val) +
                        (∑ i ∈ Finset.range 5, 2^(51 * i) * (XX[i]!).val) := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
      intro i hi
      rw [YY_plus_XX_post, Nat.mul_add]; exact Finset.mem_range.mp hi

    rw [h_X_plus_Y] at X_plus_Y_sq_post; rw [h_YY_plus_XX] at fe_post;

    have hB_equiv : (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY[i]!).val) +
                    (∑ i ∈ Finset.range 5, 2^(51 * i) * (XX[i]!).val) ≡
                    (∑ i ∈ Finset.range 5, 2^(51 * i) * (q.Y[i]!).val) ^ 2 +
                    (∑ i ∈ Finset.range 5, 2^(51 * i) * (q.X[i]!).val) ^ 2 [MOD p] := by
      apply Nat.ModEq.add; (ring_nf at *; exact YY_post); (ring_nf at *; exact XX_post)

    apply Nat.ModEq.add_left_cancel hB_equiv; rw [add_comm]
    ring_nf at *; apply Nat.ModEq.trans fe_post; exact X_plus_Y_sq_post

  · -- Goal 9.2: ⊢ Y' ∧ Z' ∧ T'
    constructor
    · -- Goal 9.2.1: Y' coordinate
      unfold Field51_as_Nat at *;
      have h_YY_plus_XX : (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY_plus_XX[i]!).val) =
                          (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY[i]!).val) +
                          (∑ i ∈ Finset.range 5, 2^(51 * i) * (XX[i]!).val) := by
        rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
        intro i hi
        rw [YY_plus_XX_post, Nat.mul_add]; exact Finset.mem_range.mp hi

      rw [← Nat.ModEq] at *; rw [h_YY_plus_XX]
      apply Nat.ModEq.add
      · exact YY_post
      · exact XX_post

    · -- Goal 9.2.2: ⊢ Z' ∧ T'
      constructor
      · -- Goal 9.2.2.1: Z' coordinate
        unfold Field51_as_Nat at *;
        rw [← Nat.ModEq] at *; ring_nf at *;

        have h_Z_dvd := Nat.modEq_iff_dvd.mp YY_minus_XX_post;
        have h_X_dvd := Nat.modEq_iff_dvd.mp XX_post;
        have h_Y_dvd := Nat.modEq_iff_dvd.mp YY_post;
        have h_X_dvd_neg := Int.dvd_neg.mpr h_X_dvd;
        have h_add_12 := Int.dvd_add h_Z_dvd h_X_dvd_neg;

        have h_all := Int.dvd_add h_Y_dvd h_add_12;

        set Y2_int := ((∑ x ∈ Finset.range 5, (q.Y[x]!).val * 2 ^ (x * 51)) ^ 2);
        set X2_int := ((∑ x ∈ Finset.range 5, (q.X[x]!).val * 2 ^ (x * 51)) ^ 2);
        set Z_int  := (∑ x ∈ Finset.range 5, (YY_minus_XX[x]!).val * 2 ^ (x * 51));
        set YY_int := (∑ x ∈ Finset.range 5, (YY[x]!).val * 2 ^ (x * 51));
        set XX_int := (∑ x ∈ Finset.range 5, (XX[x]!).val * 2 ^ (x * 51));
        have h_sub_Y : Z_int + XX_int ≡ Y2_int [MOD p] := by
          apply Nat.ModEq.trans YY_minus_XX_post YY_post
        have h_final : Z_int + X2_int ≡ Y2_int [MOD p] := by
          have h_sub_X := Nat.ModEq.add_left Z_int XX_post
          apply Nat.ModEq.trans h_sub_X.symm h_sub_Y

        apply Nat.ModEq.add_right_cancel' X2_int
        apply Nat.ModEq.trans h_final
        apply Nat.ModEq.symm
        rw [Nat.ModEq]

        sorry

      · -- Goal 9.2.2.2: T' coordinate
        -- ⊢ (∑...fe1...) % p = ( 2*(∑...q.Z^2) - (∑...q.Y^2) + (∑...q.X^2) ) % p

        sorry


end curve25519_dalek.backend.serial.curve_models.ProjectivePoint
