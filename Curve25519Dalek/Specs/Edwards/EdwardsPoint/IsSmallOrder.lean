/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang, Lacramioara Astefanoaei
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.MulByCofactor
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Identity
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.CtEq

/-!
# Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::is_small_order`

Determines whether an `EdwardsPoint` has small order, i.e. lies in the torsion subgroup `E[8]`.
A point has small order iff multiplying it by the cofactor (= 8) yields the identity element.

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Edwards curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.edwards.EdwardsPoint

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::is_small_order`**
• The function always succeeds (no panic)
• Returns `true` iff multiplying `self` by the cofactor yields the identity, i.e. `self ∈ E[8]`
-/
@[step]
theorem is_small_order_spec (self : EdwardsPoint) (hself : self.IsValid) :
    is_small_order self ⦃ (result : Bool) =>
      (result ↔ h • self.toPoint = 0) ⦄ := by
  unfold is_small_order curve25519_dalek.traits.IsIdentity.Blanket.is_identity
  step with mul_by_cofactor_spec as ⟨ep, hep_valid, hep_point⟩
  step with Insts.Curve25519_dalekTraitsIdentity.identity_spec as
    ⟨t, ht_X, ht_Y, ht_Z, ht_T, ht_valid⟩
  step with Insts.SubtleConstantTimeEq.ct_eq_spec as ⟨c, hc1, hc2⟩
  -- `grind` bridges the Array/List coercion gap (ep.X[i]! vs (↑ep.X)[i]!) and < → ≤.
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
