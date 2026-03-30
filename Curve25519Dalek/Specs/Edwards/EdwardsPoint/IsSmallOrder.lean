/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.MulByCofactor
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Identity
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.CtEq
/-!
# Spec theorem for `EdwardsPoint::is_small_order`

Specification and proof for `EdwardsPoint::is_small_order`.

This function determines if an Edwards point is of small order (i.e., if it is in E[8]).

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP Edwards
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
    is_small_order self ⦃ result =>
    (result ↔ h • self.toPoint = 0) ⦄ := by
  unfold is_small_order curve25519_dalek.traits.IsIdentity.Blanket.is_identity
  progress with mul_by_cofactor_spec as ⟨ep, hep_valid, hep_point⟩
  progress with Insts.Curve25519_dalekTraitsIdentity.identity_spec as
    ⟨t, ht_X, ht_Y, ht_Z, ht_T, ht_valid⟩
  progress with Insts.SubtleConstantTimeEq.ct_eq_spec as ⟨c, hc1, hc2⟩
  -- Grind bridges the Array/List coercion gap (ep.X[i]! vs (↑ep.X)[i]!) and < → ≤.
  -- Grind-free alternative per goal:
  --   intro i hi; have := hep_valid.X_bounds i hi
  --   simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
  --     UScalar.ofNatCore_val_eq, getElem!_pos, Nat.reducePow]; omega
  · have := hep_valid.X_bounds; grind
  · have := hep_valid.Y_bounds; grind
  · have := hep_valid.Z_bounds; grind
  · have := ht_valid.X_bounds; grind
  · have := ht_valid.Y_bounds; grind
  · have := ht_valid.Z_bounds; grind
  · simp only [Bool.Insts.CoreConvertFromChoice.from, spec_ok]
    have ht_zero : t.toPoint = 0 := by
      have ⟨htpx, htpy⟩ := EdwardsPoint.toPoint_of_isValid ht_valid
      ext
      · simp [htpx, toField, ht_X] -- closes Point.x 0 via Mathlib simp lemmas
      · simp [htpy, toField, ht_Y, ht_Z] -- closes Point.y 0 via Mathlib simp lemmas
    have hc_iff : c = Choice.one ↔ ep.toPoint = t.toPoint :=
      hc2 hep_valid ht_valid
    rw [ht_zero] at hc_iff
    rw [hep_point] at hc_iff
    simp only [decide_eq_true_eq]
    have val_iff : c.val = 1#u8 ↔ c = Choice.one := by
      cases c with | mk val valid => simp only [Choice.one, subtle.Choice.mk.injEq]
    exact val_iff.trans hc_iff

end curve25519_dalek.edwards.EdwardsPoint
