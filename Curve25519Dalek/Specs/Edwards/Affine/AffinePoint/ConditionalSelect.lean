/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect
/-! # Spec Theorem for `AffinePoint::conditional_select`

Specification and proof for the `ConditionallySelectable` trait implementation for `AffinePoint`.

This function conditionally selects between two affine Edwards points based on a `Choice` value
by applying `FieldElement51::conditional_select` component-wise to the coordinates (x, y).

Returns `b` when `choice = 1` and `a` when `choice = 0`, in constant time.

**Source**: curve25519-dalek/src/edwards/affine.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable

/-
natural language description:

- Takes two AffinePoints `a` and `b` and a `Choice` value
- Returns one of the two points based on the choice, in constant time
- Implementation: applies `FieldElement51::conditional_select` component-wise
  to the coordinates (x, y)

natural language specs:

- The function always succeeds (no panic)
- Returns `b` when `choice = 1` and `a` when `choice = 0`
-/

/--
**Spec and proof concerning
`edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable.conditional_select`**:
- No panic (always returns successfully)
- Returns `b` when `choice = 1` and `a` when `choice = 0`
-/
@[step]
theorem conditional_select_spec
    (a b : edwards.affine.AffinePoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : edwards.affine.AffinePoint) =>
      result = if choice.val = 1#u8 then b else a ⦄ := by
  unfold conditional_select
  step as ⟨feX, hfeX⟩
  step as ⟨feY, hfeY⟩
  have arr_ext : ∀ (x y : backend.serial.u64.field.FieldElement51),
      (∀ i < 5, x[i]! = y[i]!) → x = y := by
    intro x y h
    apply Subtype.ext
    rw [List.eq_iff_forall_eq_getElem!]
    exact ⟨by simp only [List.Vector.length_val], fun i hi => by
      simp only [List.getElem!_eq_getElem?_getD]
      exact h i (by scalar_tac)⟩
  by_cases h : choice.val = 1#u8
  all_goals simp only [h, ite_true, ite_false] at *
  all_goals obtain ⟨_, _⟩ := a
  all_goals obtain ⟨_, _⟩ := b
  all_goals simp only [edwards.affine.AffinePoint.mk.injEq] at *
  all_goals exact ⟨arr_ext _ _ hfeX, arr_ext _ _ hfeY⟩

end curve25519_dalek.edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable
