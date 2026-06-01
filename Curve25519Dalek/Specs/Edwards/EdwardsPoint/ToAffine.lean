/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul

/-!
# Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::to_affine`

Converts an `EdwardsPoint` from extended twisted Edwards coordinates `(X, Y, Z, T)` to
affine coordinates `(x, y)` by dehomogenizing:

- `x ≡ X / Z ≡ X * Z⁻¹ (mod p)`
- `y ≡ Y / Z ≡ Y * Z⁻¹ (mod p)`

Special case: when `Z ≡ 0 (mod p)` (a point at infinity in projective coordinates), since
`0.invert() = 0` in this implementation, the result is `(x, y) ≡ (0, 0) (mod p)`. In
practice, valid `EdwardsPoint`s have `Z ≢ 0 (mod p)`.

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Edwards curve25519_dalek.backend.serial.u64.field
namespace curve25519_dalek.edwards.EdwardsPoint

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::to_affine`**
• The function always succeeds (no panic) when the input limbs satisfy `< 2 ^ 54`
• If `Z ≡ 0 (mod p)`: `x ≡ 0 (mod p)` and `y ≡ 0 (mod p)`
• If `Z ≢ 0 (mod p)`: `x * Z ≡ X (mod p)` and `y * Z ≡ Y (mod p)`
• Output limb bounds: every limb of `ap.x` and `ap.y` is `< 2 ^ 52`
-/
theorem to_affine_spec' (self : EdwardsPoint)
    (hX : ∀ i < 5, self.X[i]!.val < 2 ^ 54)
    (hY : ∀ i < 5, self.Y[i]!.val < 2 ^ 54)
    (hZ : ∀ i < 5, self.Z[i]!.val < 2 ^ 54) :
    to_affine self ⦃ (ap : affine.AffinePoint) =>
      let X := Field51_as_Nat self.X
      let Y := Field51_as_Nat self.Y
      let Z := Field51_as_Nat self.Z
      let x := Field51_as_Nat ap.x
      let y := Field51_as_Nat ap.y
      (if Z % p = 0 then
        x % p = 0 ∧ y % p = 0
      else
        (x * Z) % p = X % p ∧
        (y * Z) % p = Y % p) ∧
      (∀ i < 5, ap.x[i]!.val < 2 ^ 52) ∧
      (∀ i < 5, ap.y[i]!.val < 2 ^ 52) ⦄ := by
  unfold to_affine
  step as ⟨Z_inv, h_inv_nonzero, h_inv_zero, h_inv_bounds⟩ -- invert self.Z
  step as ⟨x, hx_mod, hx_bounds⟩ -- mul self.X Z_inv
  step as ⟨y, hy_mod, hy_bounds⟩ -- mul self.Y Z_inv
  constructor
  · split_ifs with h_Z
    · -- Z ≡ 0 case
      have h_val : Field51_as_Nat Z_inv % p = 0 := h_inv_zero h_Z
      rw [Nat.ModEq] at hx_mod hy_mod
      constructor
      · rw [hx_mod, Nat.mul_mod, h_val, mul_zero, Nat.zero_mod]
      · rw [hy_mod, Nat.mul_mod, h_val, mul_zero, Nat.zero_mod]
    · -- Z ≢ 0 case
      have h_val : (Field51_as_Nat Z_inv % p * (Field51_as_Nat self.Z % p)) % p = 1 :=
        h_inv_nonzero h_Z
      rw [Nat.mul_mod] at h_val
      rw [Nat.ModEq] at hx_mod hy_mod
      constructor
      · rw [Nat.mul_mod, hx_mod]
        simp only [Nat.mul_mod_mod, Nat.mod_mul_mod, mul_assoc]
        simp only [dvd_refl, Nat.mod_mod_of_dvd, Nat.mul_mod_mod, Nat.mod_mul_mod] at h_val
        simp [Nat.mul_mod, h_val]
      · rw [Nat.mul_mod, hy_mod]
        simp only [Nat.mul_mod_mod, Nat.mod_mul_mod, mul_assoc]
        simp only [dvd_refl, Nat.mod_mod_of_dvd, Nat.mul_mod_mod, Nat.mod_mul_mod] at h_val
        simp [Nat.mul_mod, h_val]
  · constructor
    · intro i hi; have := hx_bounds i hi; omega
    · intro i hi; have := hy_bounds i hi; omega

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::to_affine`**
• The function always succeeds (no panic) for a valid `EdwardsPoint`
• The result is a valid affine point
• The result represents the same abstract point: `result.toPoint = self.toPoint`
-/
@[step]
theorem to_affine_spec (self : EdwardsPoint) (hself : self.IsValid) :
    to_affine self ⦃ (ap : affine.AffinePoint) =>
      ap.IsValid ∧
      ap.toPoint = self.toPoint ⦄ := by
  -- Derive < 2^54 bounds from IsValid (which gives < 2^53)
  have hX : ∀ i < 5, self.X[i]!.val < 2 ^ 54 :=
    fun i hi => by have := hself.X_bounds i hi; omega
  have hY : ∀ i < 5, self.Y[i]!.val < 2 ^ 54 :=
    fun i hi => by have := hself.Y_bounds i hi; omega
  have hZ_bnd : ∀ i < 5, self.Z[i]!.val < 2 ^ 54 :=
    fun i hi => by have := hself.Z_bounds i hi; omega
  -- Z's Nat representation isn't ≡ 0 mod p (from `Z.toField ≠ 0`)
  have hZ_mod_ne : Field51_as_Nat self.Z % p ≠ 0 := by
    intro h
    apply hself.Z_ne_zero
    unfold FieldElement51.toField
    exact lift_mod_eq _ _ (by simpa [Nat.zero_mod] using h)
  -- Apply the operational spec and weaken
  apply WP.spec_mono (to_affine_spec' self hX hY hZ_bnd)
  intro ap ⟨h_branch, h_x_bnd, h_y_bnd⟩
  -- Z ≢ 0 branch is the only reachable one
  rw [if_neg hZ_mod_ne] at h_branch
  obtain ⟨hxZ_mod, hyZ_mod⟩ := h_branch
  -- Lift modular equalities to ZMod
  have hxZ_field : ap.x.toField * self.Z.toField = self.X.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hxZ_mod
    push_cast at h; exact h
  have hyZ_field : ap.y.toField * self.Z.toField = self.Y.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hyZ_mod
    push_cast at h; exact h
  have hZ_ne : self.Z.toField ≠ 0 := hself.Z_ne_zero
  -- Derive division forms
  have hx_div : ap.x.toField = self.X.toField / self.Z.toField := by
    field_simp; exact hxZ_field
  have hy_div : ap.y.toField = self.Y.toField / self.Z.toField := by
    field_simp; exact hyZ_field
  -- Construct ap.IsValid
  have h_ap_curve :
      Ed25519.a * ap.x.toField ^ 2 + ap.y.toField ^ 2
        = 1 + Ed25519.d * ap.x.toField ^ 2 * ap.y.toField ^ 2 := by
    rw [hx_div, hy_div]
    have hcurve := hself.on_curve
    simp only at hcurve
    have hz2 : self.Z.toField ^ 2 ≠ 0 := pow_ne_zero 2 hZ_ne
    have hz4 : self.Z.toField ^ 4 ≠ 0 := pow_ne_zero 4 hZ_ne
    simp only [Ed25519] at hcurve ⊢
    simp only [div_pow]
    field_simp
    linear_combination hcurve
  have h_ap_valid : ap.IsValid := {
    x_valid := fun i hi => by have := h_x_bnd i hi; omega
    y_valid := fun i hi => by have := h_y_bnd i hi; omega
    on_curve := h_ap_curve }
  refine ⟨h_ap_valid, ?_⟩
  -- Show ap.toPoint = self.toPoint
  unfold affine.AffinePoint.toPoint EdwardsPoint.toPoint
  rw [dif_pos h_ap_valid, dif_pos hself]
  unfold EdwardsPoint.toPoint'
  ext
  · simp [hx_div]
  · simp [hy_div]

end curve25519_dalek.edwards.EdwardsPoint
