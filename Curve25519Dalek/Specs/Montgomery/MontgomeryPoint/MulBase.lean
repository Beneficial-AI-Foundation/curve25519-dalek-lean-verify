/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
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
/-! # Spec Theorem for `MontgomeryPoint::mul_base`

Specification and proof for
`curve25519_dalek::montgomery::{curve25519_dalek::montgomery::MontgomeryPoint}::mul_base`.

This function computes the Montgomery basepoint scalar multiplication by first
performing Edwards basepoint multiplication and then converting the resulting
EdwardsPoint to a MontgomeryPoint.

**Source**: curve25519-dalek/src/montgomery.rs, lines 128:4-130:5

## TODO
- Complete proof
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64
open Montgomery
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-
natural language description:

• Computes the scalar multiplication [s]B for the Montgomery basepoint by
  delegating to EdwardsPoint::mul_base and then converting to Montgomery form.

• The implementation calls `edwards.EdwardsPoint.mul_base` and then
  `edwards.EdwardsPoint.to_montgomery` on the result.

natural language specs:

• The function always succeeds (no panic)
• The returned MontgomeryPoint is the Montgomery conversion of the Edwards
  basepoint multiplication result
-/

/- **Spec and proof concerning `montgomery.MontgomeryPoint.mul_base`**:
- No panic (always returns successfully)
- Delegates to `edwards.EdwardsPoint.mul_base` and `edwards.EdwardsPoint.to_montgomery`
- The returned MontgomeryPoint is the Montgomery conversion of the Edwards basepoint result
-/

@[step]
theorem mul_base_spec (scalar : scalar.Scalar) :
    mul_base scalar ⦃ result =>
    let ep := (U8x32_as_Nat scalar.bytes) •  _root_.Edwards.basepoint
    if  ep.y=1 then
      Montgomery.MontgomeryPoint.mkPoint result = T_point
      else
      Montgomery.MontgomeryPoint.mkPoint result =
      abs_montgomery ((U8x32_as_Nat scalar.bytes) • (fromEdwards _root_.Edwards.basepoint)) ⦄
     := by
    unfold mul_base
    step with edwards.EdwardsPoint.mul_base_spec as ⟨ ep, ep_valid, ep_toPoint ⟩
    step with edwards.EdwardsPoint.to_montgomery_spec as ⟨ res, res_cond⟩
    · exact ep_valid.Y_bounds
    · exact ep_valid.Z_bounds
    · rw[← ep_toPoint]
      by_cases h : ep.toPoint.y = 1
      · simp only [h, ↓reduceIte]
        by_cases ht : Field51_as_Nat ep.Z % p = Field51_as_Nat ep.Y % p
        · simp only [ht, ↓reduceIte] at res_cond
          have := cast_zero res res_cond.left
          apply curve25519_dalek.edwards.EdwardsPoint.mkPoint_u_zero
          exact this
        · have := curve25519_dalek.edwards.EdwardsPoint.toPoint_of_isValid ep_valid
          have hZY_eq := (Montgomery.lift_mod_eq_iff (Field51_as_Nat ep.Z) (Field51_as_Nat ep.Y))
          rw [← curve25519_dalek.backend.serial.u64.field.FieldElement51.toField] at hZY_eq
          rw [← curve25519_dalek.backend.serial.u64.field.FieldElement51.toField] at hZY_eq
          rw [Nat.ModEq] at hZY_eq
          simp only [hZY_eq] at ht
          rw [h] at this
          field_simp [ep_valid.Z_ne_zero] at this
          simp only [this.right, not_true_eq_false] at ht
      · simp only [h, ↓reduceIte]
        have := curve25519_dalek.edwards.EdwardsPoint.toPoint_of_isValid ep_valid
        have hZY_eq := (Montgomery.lift_mod_eq_iff (Field51_as_Nat ep.Z) (Field51_as_Nat ep.Y))
        rw[← curve25519_dalek.backend.serial.u64.field.FieldElement51.toField] at hZY_eq
        rw[← curve25519_dalek.backend.serial.u64.field.FieldElement51.toField] at hZY_eq
        rw[Nat.ModEq] at hZY_eq
        by_cases ht : Field51_as_Nat ep.Z % p = Field51_as_Nat ep.Y % p
        · simp only [ht, ↓reduceIte] at res_cond
          simp only [hZY_eq] at ht
          rw [← ht] at this
          field_simp [ep_valid.Z_ne_zero] at this
          simp only [this.right, not_true_eq_false] at h
        · simp_all only [false_iff, ↓reduceIte]
          have := res_cond.right
          rw[← this]
          rw[Montgomery.comm_mul_fromEdwards]

end curve25519_dalek.montgomery.MontgomeryPoint
