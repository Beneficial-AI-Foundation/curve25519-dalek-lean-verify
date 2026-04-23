/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.MulBase
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.ToMontgomery
import Curve25519Dalek.Math.Edwards.Basepoint
import Curve25519Dalek.ExternallyVerified

/-!
# Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::mul_base`

Computes the scalar multiplication `[s]B` for the Montgomery basepoint, where `s` is a `Scalar`.
The implementation delegates to `EdwardsPoint::mul_base` to compute `[s]B` in Edwards form, then
calls `EdwardsPoint::to_montgomery` to convert the result to a `MontgomeryPoint`.

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64 Montgomery
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-- **Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::mul_base`**
• The function always succeeds (no panic)
• If `ep.y = 1` (where `ep := (U8x32_as_Nat scalar.bytes) • Edwards.basepoint`),
  then `mkPoint result = T_point`
• Otherwise, `mkPoint result = abs_montgomery (s • fromEdwards Edwards.basepoint)`
  where `s = U8x32_as_Nat scalar.bytes`
-/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) :
    mul_base scalar ⦃ (result : MontgomeryPoint) =>
      let ep := (U8x32_as_Nat scalar.bytes) • _root_.Edwards.basepoint
      if ep.y = 1 then
        MontgomeryPoint.mkPoint result = T_point
      else
        MontgomeryPoint.mkPoint result = abs_montgomery
          ((U8x32_as_Nat scalar.bytes) • (fromEdwards _root_.Edwards.basepoint)) ⦄ := by
  unfold mul_base
  step with edwards.EdwardsPoint.mul_base_spec as ⟨ ep, ep_valid, ep_toPoint ⟩
  step with edwards.EdwardsPoint.to_montgomery_spec as ⟨ res, res_cond ⟩
  · exact ep_valid.Y_bounds
  · exact ep_valid.Z_bounds
  · rw [← ep_toPoint]
    by_cases h : ep.toPoint.y = 1
    · simp only [h, ↓reduceIte]
      by_cases ht : Field51_as_Nat ep.Z % p = Field51_as_Nat ep.Y % p
      · simp only [ht, ↓reduceIte] at res_cond
        have := cast_zero res res_cond.left
        apply edwards.EdwardsPoint.mkPoint_u_zero
        exact this
      · have := edwards.EdwardsPoint.toPoint_of_isValid ep_valid
        have hZY_eq := (lift_mod_eq_iff (Field51_as_Nat ep.Z) (Field51_as_Nat ep.Y))
        rw [← field.FieldElement51.toField] at hZY_eq
        rw [← field.FieldElement51.toField] at hZY_eq
        rw [Nat.ModEq] at hZY_eq
        simp only [hZY_eq] at ht
        rw [h] at this
        field_simp [ep_valid.Z_ne_zero] at this
        simp only [this.right, not_true_eq_false] at ht
    · simp only [h, ↓reduceIte]
      have := edwards.EdwardsPoint.toPoint_of_isValid ep_valid
      have hZY_eq := (lift_mod_eq_iff (Field51_as_Nat ep.Z) (Field51_as_Nat ep.Y))
      rw [← field.FieldElement51.toField] at hZY_eq
      rw [← field.FieldElement51.toField] at hZY_eq
      rw [Nat.ModEq] at hZY_eq
      by_cases ht : Field51_as_Nat ep.Z % p = Field51_as_Nat ep.Y % p
      · simp only [ht, ↓reduceIte] at res_cond
        simp only [hZY_eq] at ht
        rw [← ht] at this
        field_simp [ep_valid.Z_ne_zero] at this
        simp only [this.right, not_true_eq_false] at h
      · simp_all only [false_iff, ↓reduceIte]
        have := res_cond.right
        rw [← this]
        rw [comm_mul_fromEdwards]

end curve25519_dalek.montgomery.MontgomeryPoint
