/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Montgomery.Curve
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
/-!
# Spec theorem for `ProjectiveNielsPoint::neg`

This function computes the negation of a ProjectiveNielsPoint. Given a point
N = (Y+X, Y−X, Z, 2dXY), it returns −N by swapping Y_plus_X and Y_minus_X,
keeping Z unchanged, and negating T2d.

Ed25519 negation is `(x, y) ↦ (-x, y)` in affine form; since the PNP form gives
`x ∝ (YpX - YmX)`, the `Y_plus_X ↔ Y_minus_X` swap flips the sign of `x`, while
`y ∝ (YpX + YmX)` is symmetric and unchanged.

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs, lines 503:4-510:5"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Edwards
open curve25519_dalek.Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint
open curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.backend.serial.u64.field

namespace curve25519_dalek.Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint

/-- **Spec theorem for
`Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint.neg`**:

- No panic (always returns successfully) given `self.IsValid`.
- The output is a valid `ProjectiveNielsPoint`.
- It represents `-self.toPoint` on Ed25519.

Derived by lifting the Field51-level `FieldElement51.neg_spec` postconditions
(`r.Y_plus_X = self.Y_minus_X`, `r.Y_minus_X = self.Y_plus_X`, `r.Z = self.Z`,
`r.T2d ≡ -self.T2d [mod p]` with `r.T2d[i]!.val < 2^52`) through
`ProjectiveNielsPoint.toPoint'`. `IsValid` is symmetric in `Y_plus_X`/`Y_minus_X`
at `< 2^54`, so the swap preserves `IsValid` trivially on those fields;
`Z` is unchanged; `T2d`'s strict `< 2^52` bound is supplied by the tightened
`FieldElement51.neg_spec`. -/
@[step]
theorem neg_spec
    (self : ProjectiveNielsPoint) (h_self : self.IsValid) :
    neg self ⦃ (result : ProjectiveNielsPoint) =>
      result.IsValid ∧ result.toPoint = -self.toPoint ⦄ := by
  -- Derive the `< 2^54` precondition for the Field51-level `neg_spec` from IsValid's `< 2^52`.
  have h_T2d54 : ∀ i < 5, self.T2d[i]!.val < 2 ^ 54 := fun i hi => by
    have := h_self.T2d_bounds i hi; omega
  unfold neg
  step*
  -- step* exposes:
  --   fe_post1 : Field51_as_Nat self.T2d + Field51_as_Nat fe ≡ 0 [MOD p]
  --   fe_post2 : ∀ i < 5, fe[i]!.val < 2 ^ 52
  -- Lift fe_post1 from Nat mod to CurveField: fe.toField = -self.T2d.toField.
  simp only [Montgomery.lift_mod_eq_iff, Nat.cast_add, Nat.cast_zero] at fe_post1
  rw [← FieldElement51.toField, ← FieldElement51.toField] at fe_post1
  have fe_neg : fe.toField = -self.T2d.toField := by grind
  -- Build IsValid for the swapped-and-T2d-negated record.
  have h_r_valid :
      ({ self with Y_plus_X := self.Y_minus_X, Y_minus_X := self.Y_plus_X, T2d := fe } :
        ProjectiveNielsPoint).IsValid := by
    refine
      { Z_ne_zero := ?_, T2d_relation := ?_, on_curve := ?_,
        Y_plus_X_bounds := ?_, Y_minus_X_bounds := ?_,
        Z_bounds := ?_, T2d_bounds := ?_ }
    · exact h_self.Z_ne_zero
    · -- T2d_relation: 2 * Z * T2d' = d * (YmX² - YpX²) with T2d' = -self.T2d.
      simp only
      rw [fe_neg]
      have := h_self.T2d_relation
      simp only at this
      linear_combination -this
    · -- on_curve: curve equation invariant under YpX ↔ YmX swap
      -- (both (YpX - YmX)² and (YpX + YmX)² are swap-invariant).
      simp only
      have := h_self.on_curve
      simp only at this
      linear_combination this
    · exact h_self.Y_minus_X_bounds
    · exact h_self.Y_plus_X_bounds
    · exact h_self.Z_bounds
    · exact fe_post2
  refine ⟨h_r_valid, ?_⟩
  -- toPoint = -self.toPoint componentwise, via Point.ext.
  unfold ProjectiveNielsPoint.toPoint
  simp only [h_r_valid, ↓reduceDIte, h_self, ProjectiveNielsPoint.toPoint']
  ext
  · -- x: (YmX - YpX) / (2Z) = -((YpX - YmX) / (2Z))
    simp only [Edwards.neg_x]
    field_simp
    ring
  · -- y: (YmX + YpX) / (2Z) = (YpX + YmX) / (2Z)
    simp only [Edwards.neg_y]
    ring

end curve25519_dalek.Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint

namespace curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts
namespace CoreOpsArithNegProjectiveNielsPoint

/-- **Spec theorem for the owned-value
`ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint.neg`**.

Mirrors the shared-reference `Shared0…neg_spec`; the owned `neg` is just a
one-step delegation to it (Rust source: `-&self`). Needed so that `let*`
in downstream proofs (e.g., `LookupTable.select_spec`) matches the binding
that type-class resolution produces. -/
@[step]
theorem neg_spec (self : ProjectiveNielsPoint) (h_self : self.IsValid) :
    neg self ⦃ (result : ProjectiveNielsPoint) =>
      result.IsValid ∧ result.toPoint = -self.toPoint ⦄ := by
  unfold neg
  exact Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint.neg_spec
    self h_self

end CoreOpsArithNegProjectiveNielsPoint
end curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts
