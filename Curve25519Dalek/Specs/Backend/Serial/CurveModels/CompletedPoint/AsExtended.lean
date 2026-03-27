/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Montgomery.Curve
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
/-! # Spec Theorem for `CompletedPoint::as_extended`

Specification and proof for `CompletedPoint::as_extended`.

This function implements point conversion from completed coordinates (ℙ¹ × ℙ¹) to extended
twisted Edwards coordinates (ℙ³) on the Curve25519 elliptic curve. Given a point
P = (X:Y:Z:T) in completed coordinates (i.e., with affine coordinates given via X/Z = x and Y/T = y),
it computes an equivalent representation (X':Y':Z':T') in extended coordinates
(i.e., with X'/Z' = x, Y'/Z' = y and T' = X'Y'/Z')

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field

namespace curve25519_dalek.backend.serial.curve_models.CompletedPoint

/-
natural language description:

• Takes a CompletedPoint with coordinates (X, Y, Z, T) in completed ℙ¹ × ℙ¹ representation
(i.e., with affine coordinates given via X/Z = x and Y/T = y) and returns an EdwardsPoint
(X', Y', Z', T') in extended ℙ³ representation (i.e., with X'/Z' = x, Y'/Z' = y and T' = X'Y'/Z').
Arithmetics are performed in the field 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Given an input completed point (X, Y, Z, T), the output EdwardsPoint (X', Y', Z', T') satisfies:
- X' ≡ X·T (mod p)
- Y' ≡ Y·Z (mod p)
- Z' ≡ Z·T (mod p)
- T' ≡ X·Y (mod p)
-/

/-- **Spec and proof concerning `backend.serial.curve_models.CompletedPoint.as_extended`**:
- No panic (always returns successfully)
- Given input CompletedPoint with coordinates (X, Y, Z, T), the output EdwardsPoint (X', Y', Z', T')
satisfies the conversion formulas modulo p:
- X' ≡ X·T (mod p)
- Y' ≡ Y·Z (mod p)
- Z' ≡ Z·T (mod p)
- T' ≡ X·Y (mod p)
where p = 2^255 - 19
- Output limb bounds: all coordinates have limbs < 2^52 (from mul_spec)
These formulas implement the conversion from completed ℙ¹ × ℙ¹ coordinates to extended
twisted Edwards ℙ³ coordinates.
-/
@[step]
theorem as_extended_spec (q : CompletedPoint)
  (h_q_Valid : q.IsValid) :
  as_extended q ⦃ (e : edwards.EdwardsPoint) =>
    let X := Field51_as_Nat q.X
    let Y := Field51_as_Nat q.Y
    let Z := Field51_as_Nat q.Z
    let T := Field51_as_Nat q.T
    let X' := Field51_as_Nat e.X
    let Y' := Field51_as_Nat e.Y
    let Z' := Field51_as_Nat e.Z
    let T' := Field51_as_Nat e.T
    X' % p = (X * T) % p ∧
    Y' % p = (Y * Z) % p ∧
    Z' % p = (Z * T) % p ∧
    T' % p = (X * Y) % p ∧
    (∀ i < 5, e.X[i]!.val < 2 ^ 52) ∧
    (∀ i < 5, e.Y[i]!.val < 2 ^ 52) ∧
    (∀ i < 5, e.Z[i]!.val < 2 ^ 52) ∧
    (∀ i < 5, e.T[i]!.val < 2 ^ 52) ∧
    e.IsValid ∧
    e.toPoint = q.toPoint ⦄ := by
  unfold as_extended
  have := h_q_Valid.X_valid
  simp only [FieldElement51.IsValid, Array.getElem!_Nat_eq,
    List.getElem!_eq_getElem?_getD, Nat.reducePow] at this
  have := h_q_Valid.Y_valid
  simp only [FieldElement51.IsValid, Array.getElem!_Nat_eq,
    List.getElem!_eq_getElem?_getD, Nat.reducePow] at this
  have := h_q_Valid.Z_valid
  simp only [FieldElement51.IsValid, Array.getElem!_Nat_eq,
    List.getElem!_eq_getElem?_getD, Nat.reducePow] at this
  have := h_q_Valid.T_valid
  simp only [FieldElement51.IsValid, Array.getElem!_Nat_eq,
    List.getElem!_eq_getElem?_getD, Nat.reducePow] at this
  simp only [step_simps]
  let* ⟨ fe, fe_post1, fe_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ fe1, fe1_post1, fe1_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ fe2, fe2_post1, fe2_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ fe3, fe3_post1, fe3_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  rw [← Nat.ModEq,← Nat.ModEq,← Nat.ModEq, ← Nat.ModEq]
  simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem?_pos, Option.getD_some,
    Array.getElem!_Nat_eq, getElem!_pos, Nat.reducePow, implies_true, true_and]
  rw[Montgomery.lift_mod_eq_iff] at fe_post1
  rw[Montgomery.lift_mod_eq_iff] at fe1_post1
  rw[Montgomery.lift_mod_eq_iff] at fe2_post1
  rw[Montgomery.lift_mod_eq_iff] at fe3_post1
  have :({ X := fe, Y := fe1, Z := fe2, T := fe3 }:edwards.EdwardsPoint).IsValid := by
    constructor
    · grind
    · grind
    · grind
    · grind
    · have := h_q_Valid.T_ne_zero
      unfold FieldElement51.toField at this
      have := h_q_Valid.Z_ne_zero
      unfold FieldElement51.toField at this
      unfold FieldElement51.toField
      simp only [fe2_post1, Nat.cast_mul, ne_eq, mul_eq_zero, not_or]
      grind
    · simp only
      unfold FieldElement51.toField
      grind
    · simp only
      have :=  h_q_Valid.on_curve
      unfold FieldElement51.toField at this
      simp only at this
      unfold FieldElement51.toField
      grind
  simp only [this, true_and]
  unfold toPoint   edwards.EdwardsPoint.toPoint
  simp only [this, ↓reduceDIte, h_q_Valid]
  unfold edwards.EdwardsPoint.toPoint'
  simp only [Edwards.Point.mk.injEq]
  unfold FieldElement51.toField
  have := h_q_Valid.T_ne_zero
  unfold FieldElement51.toField at this
  have := h_q_Valid.Z_ne_zero
  unfold FieldElement51.toField at this
  simp_all only [Nat.cast_mul, ne_eq]
  grind

end curve25519_dalek.backend.serial.curve_models.CompletedPoint
