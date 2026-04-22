/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Math.Montgomery.Curve
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.EdwardsD2
import Curve25519Dalek.Aux

/-! # Spec Theorem for `EdwardsPoint::as_projective_niels`

Specification and proof for `EdwardsPoint::as_projective_niels`.

This function converts an EdwardsPoint to a ProjectiveNielsPoint, which is a
representation optimized for point addition operations.

Source: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek.backend.serial.u64.field.FieldElement51
  curve25519_dalek.backend.serial.u64.constants
open curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint
open curve25519_dalek.montgomery
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Converts an EdwardsPoint from extended twisted Edwards coordinates (X, Y, Z, T)
to ProjectiveNiels coordinates (A, B, Z', C), where:
  - A ≡ Y + X (mod p)
  - B ≡ Y - X (mod p)
  - Z' = Z (unchanged)
  - C ≡ T * 2 * d (mod p)

natural language specs:

• The function always succeeds (no panic)
• For the input Edwards point (X, Y, Z, T), the resulting ProjectiveNielsPoint has coordinates:
  - A ≡ Y + X (mod p)
  - B ≡ Y - X (mod p)
  - Z' = Z
  - C ≡ T * 2 * d (mod p)
where p = 2^255 - 19
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.as_projective_niels`**:
- No panic (always returns successfully)
- For the input Edwards point (X, Y, Z, T), the resulting ProjectiveNielsPoint has coordinates:
  - A ≡ Y + X (mod p)
  - B ≡ Y - X (mod p)
  - Z' = Z
  - C ≡ T * 2 * d (mod p)
where p = 2^255 - 19
-/
@[step]
theorem as_projective_niels_spec (e : EdwardsPoint)
    (he : e.IsValid) :
    as_projective_niels e ⦃ (pn : backend.serial.curve_models.ProjectiveNielsPoint) =>
      let X := Field51_as_Nat e.X
      let Y := Field51_as_Nat e.Y
      let Z := Field51_as_Nat e.Z
      let T := Field51_as_Nat e.T
      let A := Field51_as_Nat pn.Y_plus_X
      let B := Field51_as_Nat pn.Y_minus_X
      let Z' := Field51_as_Nat pn.Z
      let C := Field51_as_Nat pn.T2d
      A % p = (Y + X) % p ∧
      (B + X) % p = Y % p ∧
      Z' % p = Z % p ∧
      C % p = (T * (2 * d)) % p ∧
      (∀ i < 5, (pn.Y_plus_X[i]!).val < 2 ^ 54 ∧
      ∀ i < 5, (pn.Y_minus_X[i]!).val < 2 ^ 52 ∧
      ∀ i < 5, (pn.Z[i]!).val < 2 ^ 53 ∧
      ∀ i < 5, (pn.T2d[i]!).val < 2 ^ 52) ∧
      pn.IsValid ∧
      e.toPoint = pn.toPoint
       ⦄ := by
  unfold as_projective_niels
  step*
  · exact he.Y_bounds
  · have:= he.X_bounds
    exact this
  · have:= he.T_bounds
    grind
  · refine ⟨?_, ?_, ?_, ?_⟩
    · congr 1; exact pointwise_add_Field51_as_Nat e.Y e.X fe fe_post1
    · assumption
    · simp_all [Nat.ModEq]
    · constructor
      · have := he.Z_bounds
        simp_all
      · have := pointwise_add_Field51_as_Nat e.Y e.X fe fe_post1
        rw[← Nat.ModEq,Montgomery.lift_mod_eq_iff] at fe1_post2
        have : (Field51_as_Nat fe1) =
            (Field51_as_Nat e.Y) - ((Field51_as_Nat e.X) : Edwards.CurveField) := by grind
        rw[Montgomery.lift_mod_eq_iff] at fe3_post1
        have : ({ Y_plus_X := fe, Y_minus_X := fe1, Z := e.Z, T2d := fe3 } :
            backend.serial.curve_models.ProjectiveNielsPoint).IsValid := by
          refine
            { Z_ne_zero := ?_, T2d_relation := ?_, on_curve := ?_,
              Y_plus_X_bounds := ?_, Y_minus_X_bounds := ?_,
              Z_bounds := ?_, T2d_bounds := ?_ }
          · have := he.Z_ne_zero
            simp_all
          · unfold toField
            simp_all
            have := he.T_relation
            simp only  at this
            unfold toField at this
            ring_nf
            have:Edwards.Ed25519.d=d:=rfl
            grind
          · unfold toField
            simp_all
            have := he.on_curve
            simp only at this
            unfold toField at this
            grind
          · simp_all  -- Y_plus_X_bounds: < 2^54
          · -- Y_minus_X_bounds: goal < 2^54, fact fe1_post1 : < 2^52
            intro i hi; have := fe1_post1 i hi; agrind
          · have := he.Z_bounds
            simp_all
          · -- T2d_bounds: < 2^52
            intro i hi; have := fe3_post2 i hi; agrind
        simp only [this, true_and]
        unfold toPoint curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.toPoint
        simp only [he, ↓reduceDIte, this]
        unfold toPoint'
          curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.toPoint' toField
        simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
          UScalar.ofNatCore_val_eq, getElem!_pos, Nat.reducePow, Nat.cast_add,
          sub_add_cancel, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_ofNat,
          add_sub_sub_cancel, add_add_sub_cancel, Edwards.Point.mk.injEq]
        have := he.Z_ne_zero
        unfold toField at this
        field_simp
        grind

end curve25519_dalek.edwards.EdwardsPoint
