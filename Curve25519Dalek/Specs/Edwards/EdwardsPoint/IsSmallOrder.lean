/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.MulByCofactor
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Identity
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.CtEq
import Curve25519Dalek.Math.Edwards.Representation

/-! # Spec Theorem for `EdwardsPoint::is_small_order`

Specification and proof for `EdwardsPoint::is_small_order`.

This function determines if an Edwards point is of small order (i.e., if it is in E[8]).

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result Edwards
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Determines whether an EdwardsPoint is in the torsion subgroup E[8]

• A point has small order if multiplying it by the cofactor (= 8) results in the identity element

natural language specs:

• The function always succeeds (no panic)
• Returns `true` if and only if the point is in the torsion subgroup E[8]
• Equivalently, returns `true` iff multiplying by the cofactor yields the identity element
-/

/-- **Spec for `edwards.EdwardsPoint.is_small_order`**:
- Returns `true` if and only if the point has small order (is in the torsion subgroup E[8])
- This is determined by checking if multiplying by the cofactor yields the identity element
-/
@[progress]
theorem is_small_order_spec (self : EdwardsPoint) (hself : self.IsValid) :
    ∃ result : Bool, is_small_order self = ok result ∧
    (result ↔ h • self.toPoint = 0) := by
  unfold is_small_order
  unfold traits.IsIdentity.Blanket.is_identity subtle.ConstantTimeEqEdwardsPoint
    traits.IdentityEdwardsPoint core.convert.FromBoolChoice subtle.FromBoolChoice.from
  progress*
  · intro i hi; have := ep_post_1.X_bounds i hi; scalar_tac
  · intro i hi; have := ep_post_1.Y_bounds i hi; scalar_tac
  · intro i hi; have := ep_post_1.Z_bounds i hi; scalar_tac
  · intro i _; simp_all only [ONE, ONE_body, ZERO, ZERO_body]; interval_cases i <;> decide
  · intro i _; simp_all only [ONE, ONE_body, ZERO, ZERO_body]; interval_cases i <;> decide
  · intro i _; simp_all only [ONE, ONE_body, ZERO, ZERO_body]; interval_cases i <;> decide
  · rw [decide_eq_true_eq]
    have val_eq_one_iff : c.val = 1#u8 ↔ c = Choice.one := by cases c; simp [Choice.one]
    have hZERO : Field51_as_Nat ZERO = 0 := by simp [ZERO]; decide
    have hONE : Field51_as_Nat ONE = 1 := by simp [ONE]; decide
    constructor
    · -- Forward: c.val = 1#u8 → 8 • self.toPoint = 0
      intro hc
      rw [val_eq_one_iff, c_post] at hc
      simp only [t_post_1, t_post_2, t_post_3, hZERO, hONE, mul_one, zero_mul] at hc
      obtain ⟨hX_eq, hY_eq⟩ := hc
      have hX_F : ep.X.toField = 0 := by unfold toField; exact lift_mod_eq _ _ hX_eq
      have hY_F : ep.Y.toField = ep.Z.toField := by
        unfold toField; simp only [one_mul] at hY_eq; exact lift_mod_eq _ _ hY_eq
      have : ep.toPoint = 0 := by
        have ⟨hpx, hpy⟩ := EdwardsPoint.toPoint_of_isValid ep_post_1
        ext <;> simp [hpx, hpy, hX_F, hY_F, ep_post_1.Z_ne_zero]
      grind
    · -- Backward: 8 • self.toPoint = 0 → c.val = 1#u8
      intro hsmall
      rw [val_eq_one_iff, c_post]
      have hep_zero : ep.toPoint = 0 := by
        simp only [ep_post_2] at hsmall ⊢; exact hsmall
      have ⟨hpx, hpy⟩ := EdwardsPoint.toPoint_of_isValid ep_post_1
      have hX_zero : ep.X.toField / ep.Z.toField = 0 := by simp [← hpx, hep_zero]
      have hY_one : ep.Y.toField / ep.Z.toField = 1 := by simp [← hpy, hep_zero]
      simp only [t_post_1, t_post_2, t_post_3, hZERO, hONE, mul_one, zero_mul]
      have hX_field : ep.X.toField = 0 := by
        field_simp [ep_post_1.Z_ne_zero] at hX_zero; exact hX_zero
      have hY_field : ep.Y.toField = ep.Z.toField := by
        field_simp [ep_post_1.Z_ne_zero] at hY_one; exact hY_one
      unfold toField at hX_field hY_field
      exact ⟨(ZMod.natCast_eq_natCast_iff _ 0 p).mp hX_field,
             by simp only [one_mul]; exact (ZMod.natCast_eq_natCast_iff _ _ p).mp hY_field⟩

end curve25519_dalek.edwards.EdwardsPoint
