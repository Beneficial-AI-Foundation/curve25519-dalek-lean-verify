/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Math.Montgomery.Curve
/-! # Spec Theorem for `EdwardsPoint::neg`

Specification and proof for the `Neg` trait implementation for Edwards points.

This function negates an Edwards point via elliptic curve negation: it negates the
X and T coordinates while keeping Y and Z unchanged, which corresponds to negating
the x-coordinate in affine form.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.edwards.EdwardsPoint
open curve25519_dalek.backend.serial.u64.field
namespace curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint

/-
natural language description:

• Takes an EdwardsPoint `self`
• Returns its negation as an EdwardsPoint via elliptic curve group negation
• Implementation: negates the X and T coordinates while keeping Y and Z unchanged

natural language specs:

• The function always succeeds (no panic) for valid input Edwards points
• The result is a valid Edwards point
• The result represents the negation of the input (in the context of elliptic curve negation)
-/

/-- **Spec and proof concerning `Shared0EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint.neg`**:
• The function always succeeds (no panic) for valid inputs
• The result is a valid Edwards point
• The result represents the negation of the input (in the context of elliptic curve negation)
-/
@[step]
theorem neg_spec
    (self : edwards.EdwardsPoint)
    (h_self_valid : self.IsValid) :
    neg self ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = -self.toPoint ⦄ := by
  unfold neg
  have := h_self_valid.X_bounds
  have := h_self_valid.Y_bounds
  have := h_self_valid.Z_bounds
  have := h_self_valid.T_bounds
  step*
  simp only [Montgomery.lift_mod_eq_iff, Nat.cast_add, Nat.cast_zero] at fe_post1
  rw[← FieldElement51.toField, ← FieldElement51.toField ] at fe_post1
  simp only [Montgomery.lift_mod_eq_iff, Nat.cast_add, Nat.cast_zero] at fe1_post1
  rw[← FieldElement51.toField, ← FieldElement51.toField ] at fe1_post1
  have fe_neg: fe.toField=-self.X.toField  := by grind
  have fe1_neg: fe1.toField =-self.T.toField := by grind
  have : ({ X := fe, Y := self.Y, Z := self.Z, T := fe1 }:edwards.EdwardsPoint).IsValid := by
    constructor
    · grind
    · grind
    · grind
    · grind
    · have := h_self_valid.Z_ne_zero
      simp[this]
    · have := h_self_valid.T_relation
      simp only
      rw[fe_neg, fe1_neg]
      grind
    · simp only
      rw[fe_neg]
      have := h_self_valid.on_curve
      simp at this
      grind
  unfold toPoint
  simp only [this, ↓reduceDIte, toPoint', h_self_valid, true_and, fe_neg]
  ext
  · simp only [Edwards.neg_x]
    field_simp
  · simp only [Edwards.neg_y]












end curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint
