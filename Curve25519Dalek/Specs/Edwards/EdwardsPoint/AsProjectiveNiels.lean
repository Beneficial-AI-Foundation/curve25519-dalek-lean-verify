/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
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

/-!
# Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::as_projective_niels`

Convert an EdwardsPoint from extended twisted Edwards coordinates `(X, Y, Z, T)` to
ProjectiveNiels coordinates `(A, B, Z', C)`, a representation optimized for point
addition operations. Working modulo `p = 2^255 - 19`, the formulas are:
- `A ≡ Y + X (mod p)`
- `B ≡ Y - X (mod p)`
- `Z' = Z` (unchanged)
- `C ≡ T · 2 · d (mod p)`

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51
  curve25519_dalek.backend.serial.u64.constants
  curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint
  curve25519_dalek.montgomery
namespace curve25519_dalek.edwards.EdwardsPoint

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::as_projective_niels`**
• The function always succeeds (no panic) for valid input EdwardsPoints
• The resulting `Y_plus_X` limb representation `A` satisfies `A ≡ Y + X (mod p)`
• The resulting `Y_minus_X` limb representation `B` satisfies `B + X ≡ Y (mod p)`
• The resulting `Z` limb representation `Z'` satisfies `Z' ≡ Z (mod p)`
• The resulting `T2d` limb representation `C` satisfies `C ≡ T · (2 · d) (mod p)`
• Limb bounds: `Y_plus_X` < 2^54, `Y_minus_X` < 2^52, `Z` < 2^53, `T2d` < 2^52
• The result is a valid `ProjectiveNielsPoint`
• The result represents the same elliptic curve point as the input
-/
@[step]
theorem as_projective_niels_spec
    (self : EdwardsPoint)
    (hself : self.IsValid) :
    as_projective_niels self ⦃ (pn : backend.serial.curve_models.ProjectiveNielsPoint) =>
      let X := Field51_as_Nat self.X
      let Y := Field51_as_Nat self.Y
      let Z := Field51_as_Nat self.Z
      let T := Field51_as_Nat self.T
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
      self.toPoint = pn.toPoint ⦄ := by
  unfold as_projective_niels
  step*
  · exact hself.Y_bounds
  · have := hself.X_bounds
    exact this
  · have := hself.T_bounds
    -- mathlib v4.30 drift: grind needs Array.getElem!_Nat_eq hint
    grind [Array.getElem!_Nat_eq]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · congr 1; exact pointwise_add_Field51_as_Nat self.Y self.X fe fe_post1
    · assumption
    · simp_all [Nat.ModEq]
    · constructor
      · have := hself.Z_bounds
        simp_all
      · have := pointwise_add_Field51_as_Nat self.Y self.X fe fe_post1
        rw [← Nat.ModEq, Montgomery.lift_mod_eq_iff] at fe1_post2
        have : (Field51_as_Nat fe1) =
            (Field51_as_Nat self.Y) - ((Field51_as_Nat self.X) : Edwards.CurveField) := by grind
        rw [Montgomery.lift_mod_eq_iff] at fe3_post1
        have : ({ Y_plus_X := fe, Y_minus_X := fe1, Z := self.Z, T2d := fe3 } :
            backend.serial.curve_models.ProjectiveNielsPoint).IsValid := by
          refine
            { Z_ne_zero := ?_, T2d_relation := ?_, on_curve := ?_,
              Y_plus_X_bounds := ?_, Y_minus_X_bounds := ?_,
              Z_bounds := ?_, T2d_bounds := ?_ }
          · have := hself.Z_ne_zero
            simp_all
          · unfold toField
            simp_all only
            have := hself.T_relation
            simp only at this
            unfold toField at this
            ring_nf
            have : Edwards.Ed25519.d = d := rfl
            grind
          · unfold toField
            simp_all only
            have := hself.on_curve
            simp only at this
            unfold toField at this
            grind
          · simp_all  -- Y_plus_X_bounds: < 2^54
          · -- Y_minus_X_bounds: goal < 2^54, fact fe1_post1 : < 2^52
            -- mathlib v4.30 drift: agrind no longer closes; use grind with hint
            intro i hi; have := fe1_post1 i hi; grind [Array.getElem!_Nat_eq]
          · have := hself.Z_bounds
            simp_all
          · -- T2d_bounds: < 2^52
            -- mathlib v4.30 drift: agrind no longer closes; use grind with hint
            intro i hi; have := fe3_post2 i hi; grind [Array.getElem!_Nat_eq]
        simp only [this, true_and]
        unfold toPoint backend.serial.curve_models.ProjectiveNielsPoint.toPoint
        simp only [hself, ↓reduceDIte, this]
        unfold toPoint'
          backend.serial.curve_models.ProjectiveNielsPoint.toPoint' toField
        simp_all only
        have := hself.Z_ne_zero
        unfold toField at this
        field_simp
        -- mathlib v4.30 drift: grind can't close; use congr+push_cast+field_simp+ring
        congr 1 <;> push_cast <;> field_simp <;> ring

end curve25519_dalek.edwards.EdwardsPoint
