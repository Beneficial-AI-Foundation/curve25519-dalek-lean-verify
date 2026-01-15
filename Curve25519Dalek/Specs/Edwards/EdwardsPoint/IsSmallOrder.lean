/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.MulByCofactor
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Identity
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.CtEq

/-! # Spec Theorem for `EdwardsPoint::is_small_order`

Specification and proof for `EdwardsPoint::is_small_order`.

This function determines if an Edwards point is of small order (i.e., if it is in E[8]).

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result Edwards
open curve25519_dalek.backend.serial.u64.field.FieldElement51 (toField)
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

/-- **Spec and proof concerning `edwards.EdwardsPoint.is_small_order`**:
- Returns `true` if and only if the point has small order (is in the torsion subgroup E[8])
- This is determined by checking if multiplying by the cofactor yields the identity element
-/
@[progress]
theorem is_small_order_spec (self : EdwardsPoint) (hself : self.IsValid) :
    ∃ result : Bool, is_small_order self = ok result ∧
    (result ↔ 8 • self.toPoint = 0) := by
    unfold is_small_order
    unfold traits.IsIdentity.Blanket.is_identity subtle.ConstantTimeEqEdwardsPoint traits.IdentityEdwardsPoint
    unfold core.convert.FromBoolChoice subtle.FromBoolChoice.from
    /- Rust source:
    pub fn is_small_order(&self) -> bool {
        self.mul_by_cofactor().is_identity()
    }
    -/
    progress*
    · intro i hi; have := ep_post_1.X_bounds i hi; scalar_tac
    · intro i hi; have := ep_post_1.Y_bounds i hi; scalar_tac
    · intro i hi; have := ep_post_1.Z_bounds i hi; scalar_tac
    · intro i hi
      simp_all only [backend.serial.u64.field.FieldElement51.ONE,
                     backend.serial.u64.field.FieldElement51.ONE_body,
                     backend.serial.u64.field.FieldElement51.ZERO,
                     backend.serial.u64.field.FieldElement51.ZERO_body]
      interval_cases i <;> native_decide
    · intro i hi
      simp_all only [backend.serial.u64.field.FieldElement51.ONE,
                     backend.serial.u64.field.FieldElement51.ONE_body,
                     backend.serial.u64.field.FieldElement51.ZERO,
                     backend.serial.u64.field.FieldElement51.ZERO_body]
      interval_cases i <;> native_decide
    · intro i hi
      simp_all only [backend.serial.u64.field.FieldElement51.ONE,
                     backend.serial.u64.field.FieldElement51.ONE_body,
                     backend.serial.u64.field.FieldElement51.ZERO,
                     backend.serial.u64.field.FieldElement51.ZERO_body]
      interval_cases i <;> native_decide
    · rw [decide_eq_true_eq]
      -- c_post : c = Choice.one ↔ (modular conditions)
      -- ep_post_2 : ep.toPoint = h • self.toPoint (h = 8)
      -- t is the identity with X = ZERO, Y = ONE, Z = ONE, T = ZERO
      -- Helper lemma for Choice conversion
      have val_eq_one_iff : c.val = 1#u8 ↔ c = Choice.one := by
        cases c with | mk val valid =>
        simp [Choice.one]
      constructor
      · -- Forward: c.val = 1#u8 → 8 • self.toPoint = 0
        intro hc
        -- c = Choice.one means ep equals identity (in projective coords)
        rw [val_eq_one_iff, c_post] at hc
        -- The identity has Field51_as_Nat of X = 0, Y = 1, Z = 1
        have hZERO : Field51_as_Nat backend.serial.u64.field.FieldElement51.ZERO = 0 := by
          simp only [backend.serial.u64.field.FieldElement51.ZERO,
                     backend.serial.u64.field.FieldElement51.ZERO_body]; decide
        have hONE : Field51_as_Nat backend.serial.u64.field.FieldElement51.ONE = 1 := by
          simp only [backend.serial.u64.field.FieldElement51.ONE,
                     backend.serial.u64.field.FieldElement51.ONE_body]; decide
        -- Simplify using t's coordinates
        simp only [t_post_1, t_post_2, t_post_3, hZERO, hONE] at hc
        simp only [mul_one, zero_mul] at hc
        obtain ⟨hX_eq, hY_eq⟩ := hc
        -- hX_eq : Field51_as_Nat ep.X ≡ 0 [MOD p]
        -- hY_eq : Field51_as_Nat ep.Y ≡ Field51_as_Nat ep.Z [MOD p]
        -- This means in CurveField: ep.X.toField = 0 and ep.Y.toField = ep.Z.toField
        have hX_F : ep.X.toField = 0 := by
          unfold backend.serial.u64.field.FieldElement51.toField
          rw [Nat.ModEq] at hX_eq
          have := lift_mod_eq _ _ hX_eq
          simp at this; exact this
        have hY_F : ep.Y.toField = ep.Z.toField := by
          unfold backend.serial.u64.field.FieldElement51.toField
          rw [Nat.ModEq] at hY_eq
          simp only [one_mul] at hY_eq
          exact lift_mod_eq _ _ hY_eq
        -- Therefore ep.toPoint = (0, 1) = 0
        have hep_zero : ep.toPoint = 0 := by
          have ⟨hpx, hpy⟩ := EdwardsPoint.toPoint_of_isValid ep_post_1
          ext
          · rw [hpx, hX_F, zero_div]; rfl
          · rw [hpy, hY_F, div_self (ep_post_1.Z_ne_zero)]; rfl
        -- Use ep.toPoint = h • self.toPoint (h = 8)
        have hh : h = 8 := rfl
        rw [← hh, ← ep_post_2, hep_zero]
      · -- Backward: 8 • self.toPoint = 0 → c.val = 1#u8
        intro hsmall
        rw [val_eq_one_iff, c_post]
        -- 8 • self.toPoint = 0 means ep.toPoint = 0
        have hh : _root_.h = 8 := rfl
        rw [← hh] at hsmall  -- Now hsmall : h • self.toPoint = 0
        have hep_zero : ep.toPoint = 0 := by rw [ep_post_2]; exact hsmall
        -- Extract coordinates from ep.toPoint = 0
        have ⟨hpx, hpy⟩ := EdwardsPoint.toPoint_of_isValid ep_post_1
        have hX_zero : ep.X.toField / ep.Z.toField = 0 := by rw [← hpx, hep_zero]; simp
        have hY_one : ep.Y.toField / ep.Z.toField = 1 := by rw [← hpy, hep_zero]; simp
        -- From these, deduce the modular conditions
        have hZERO : Field51_as_Nat backend.serial.u64.field.FieldElement51.ZERO = 0 := by
          simp only [backend.serial.u64.field.FieldElement51.ZERO,
                     backend.serial.u64.field.FieldElement51.ZERO_body]; decide
        have hONE : Field51_as_Nat backend.serial.u64.field.FieldElement51.ONE = 1 := by
          simp only [backend.serial.u64.field.FieldElement51.ONE,
                     backend.serial.u64.field.FieldElement51.ONE_body]; decide
        simp only [t_post_1, t_post_2, t_post_3, hZERO, hONE, mul_one, zero_mul]
        constructor
        · -- Field51_as_Nat ep.X ≡ 0 [MOD p]
          rw [Nat.ModEq]
          have hX_field : ep.X.toField = 0 := by
            have hz := ep_post_1.Z_ne_zero
            field_simp [hz] at hX_zero; exact hX_zero
          unfold backend.serial.u64.field.FieldElement51.toField at hX_field
          have := (ZMod.natCast_eq_natCast_iff (Field51_as_Nat ep.X) 0 p).mp hX_field
          simp at this; exact this
        · -- Field51_as_Nat ep.Y ≡ 1 * Field51_as_Nat ep.Z [MOD p]
          simp only [one_mul]
          rw [Nat.ModEq]
          have hY_field : ep.Y.toField = ep.Z.toField := by
            have hz := ep_post_1.Z_ne_zero
            field_simp [hz] at hY_one; exact hY_one
          unfold backend.serial.u64.field.FieldElement51.toField at hY_field
          exact (ZMod.natCast_eq_natCast_iff _ _ p).mp hY_field

end curve25519_dalek.edwards.EdwardsPoint
