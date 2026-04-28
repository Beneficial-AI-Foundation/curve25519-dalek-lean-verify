/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul

/-! # Spec Theorem for `EdwardsPoint::to_affine`

Specification and proof for `EdwardsPoint::to_affine`.

This function converts an EdwardsPoint from extended twisted Edwards coordinates (X, Y, Z, T)
to affine coordinates (x, y) by dehomogenizing: x = X/Z, y = Y/Z.

Two specs are exposed:
- `to_affine_spec'` — operational form. Requires only limb bounds (`< 2^54`) and gives
  raw modular equalities + output bounds. Handles the degenerate `Z ≡ 0` case explicitly.
  Not tagged `@[step]` — used internally by `to_affine_spec`.
- `to_affine_spec` — math-bridged form. Requires `e.IsValid` and gives the clean
  postcondition `result.IsValid ∧ result.toPoint = self.toPoint` in `Point Ed25519`.
  Tagged `@[step]` — preferred form for chaining in downstream proofs.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Edwards
open curve25519_dalek.backend.serial.u64.field
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Converts an EdwardsPoint from extended twisted Edwards coordinates (X, Y, Z, T)
to affine coordinates (x, y), where:
  - x ≡ X/Z ≡ X * Z^(-1) (mod p)
  - y ≡ Y/Z ≡ Y * Z^(-1) (mod p)

• Special case: when Z ≡ 0 (mod p) (a point at infinity in projective coordinates),
  since 0.invert() = 0 in this implementation, the result will be x ≡ 0, y ≡ 0 (mod p).
  However, in practice, valid EdwardsPoints should have Z ≢ 0 (mod p).

natural language specs (operational form `to_affine_spec'`):

• The function always succeeds (no panic) when input limbs satisfy bounds
• For the input Edwards point (X, Y, Z, T), it holds for the resulting AffinePoint:
  - If Z ≢ 0 (mod p): x * Z ≡ X (mod p) and y * Z ≡ Y (mod p)
  - If Z ≡ 0 (mod p): x ≡ 0 (mod p) and y ≡ 0 (mod p)
where p = 2^255 - 19
-/

/-- **Operational spec for `edwards.EdwardsPoint.to_affine`**:
- No panic (always returns successfully)
- For the input Edwards point (X, Y, Z, T), the resulting AffinePoint has coordinates:
  - If Z ≡ 0 (mod p): x ≡ 0 (mod p) and y ≡ 0 (mod p)
  - If Z ≢ 0 (mod p): x * Z ≡ X (mod p) and y * Z ≡ Y (mod p)
- Output limb bounds: `< 2^52` on `ap.x` and `ap.y`

This is the primitive form. Use `to_affine_spec` (math-bridged) in downstream proofs.
-/
theorem to_affine_spec' (e : EdwardsPoint)
    (hX : ∀ i < 5, e.X[i]!.val < 2 ^ 54)
    (hY : ∀ i < 5, e.Y[i]!.val < 2 ^ 54)
    (hZ : ∀ i < 5, e.Z[i]!.val < 2 ^ 54) :
    to_affine e ⦃ ap =>
      let X := Field51_as_Nat e.X
      let Y := Field51_as_Nat e.Y
      let Z := Field51_as_Nat e.Z
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
    step as ⟨Z_inv, h_inv_nonzero, h_inv_zero, h_inv_bounds⟩  -- invert e.Z
    step as ⟨x, hx_mod, hx_bounds⟩  -- mul e.X Z_inv
    step as ⟨y, hy_mod, hy_bounds⟩  -- mul e.Y Z_inv
    constructor
    · split_ifs with h_Z
      · -- Z ≡ 0 case
        have h_val : Field51_as_Nat Z_inv % p = 0 := h_inv_zero h_Z
        rw [Nat.ModEq] at hx_mod hy_mod
        constructor
        · rw [hx_mod, Nat.mul_mod, h_val, mul_zero, Nat.zero_mod]
        · rw [hy_mod, Nat.mul_mod, h_val, mul_zero, Nat.zero_mod]
      · -- Z ≢ 0 case
        have h_val : (Field51_as_Nat Z_inv % p * (Field51_as_Nat e.Z % p)) % p = 1 :=
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

/-- **Spec and proof concerning `edwards.EdwardsPoint.to_affine`** (math-bridged):
- Requires `self.IsValid` (limbs `< 2^53`, `Z ≠ 0`, extended relation, curve equation).
- Ensures `result.IsValid` (the affine point satisfies the curve equation).
- Math bridge: `result.toPoint = self.toPoint` in `Point Ed25519`.

Wraps the operational `to_affine_spec'` and lifts its Nat-modular postconditions to
the abstract `Point Ed25519` group.
-/
@[step]
theorem to_affine_spec (e : EdwardsPoint) (hself : e.IsValid) :
    to_affine e ⦃ ap =>
      ap.IsValid ∧
      ap.toPoint = e.toPoint ⦄ := by
  -- Derive < 2^54 bounds from IsValid (which gives < 2^53)
  have hX : ∀ i < 5, e.X[i]!.val < 2 ^ 54 :=
    fun i hi => by have := hself.X_bounds i hi; omega
  have hY : ∀ i < 5, e.Y[i]!.val < 2 ^ 54 :=
    fun i hi => by have := hself.Y_bounds i hi; omega
  have hZ_bnd : ∀ i < 5, e.Z[i]!.val < 2 ^ 54 :=
    fun i hi => by have := hself.Z_bounds i hi; omega
  -- Z's Nat representation isn't ≡ 0 mod p (from `Z.toField ≠ 0`)
  have hZ_mod_ne : Field51_as_Nat e.Z % p ≠ 0 := by
    intro h
    apply hself.Z_ne_zero
    unfold FieldElement51.toField
    exact lift_mod_eq _ _ (by simpa [Nat.zero_mod] using h)
  -- Apply the operational spec and weaken
  apply WP.spec_mono (to_affine_spec' e hX hY hZ_bnd)
  intro ap ⟨h_branch, h_x_bnd, h_y_bnd⟩
  -- Z ≢ 0 branch is the only reachable one
  rw [if_neg hZ_mod_ne] at h_branch
  obtain ⟨hxZ_mod, hyZ_mod⟩ := h_branch
  -- Lift modular equalities to ZMod
  have hxZ_field : ap.x.toField * e.Z.toField = e.X.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hxZ_mod
    push_cast at h; exact h
  have hyZ_field : ap.y.toField * e.Z.toField = e.Y.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hyZ_mod
    push_cast at h; exact h
  have hZ_ne : e.Z.toField ≠ 0 := hself.Z_ne_zero
  -- Derive division forms
  have hx_div : ap.x.toField = e.X.toField / e.Z.toField := by
    field_simp; exact hxZ_field
  have hy_div : ap.y.toField = e.Y.toField / e.Z.toField := by
    field_simp; exact hyZ_field
  -- Construct ap.IsValid
  have h_ap_curve :
      Ed25519.a * ap.x.toField ^ 2 + ap.y.toField ^ 2
        = 1 + Ed25519.d * ap.x.toField ^ 2 * ap.y.toField ^ 2 := by
    rw [hx_div, hy_div]
    have hcurve := hself.on_curve
    simp only at hcurve
    have hz2 : e.Z.toField ^ 2 ≠ 0 := pow_ne_zero 2 hZ_ne
    have hz4 : e.Z.toField ^ 4 ≠ 0 := pow_ne_zero 4 hZ_ne
    simp only [Ed25519] at hcurve ⊢
    simp only [div_pow]
    field_simp
    linear_combination hcurve
  have h_ap_valid : ap.IsValid := {
    x_valid := fun i hi => by have := h_x_bnd i hi; omega
    y_valid := fun i hi => by have := h_y_bnd i hi; omega
    on_curve := h_ap_curve }
  refine ⟨h_ap_valid, ?_⟩
  -- Show ap.toPoint = e.toPoint
  unfold edwards.affine.AffinePoint.toPoint EdwardsPoint.toPoint
  rw [dif_pos h_ap_valid, dif_pos hself]
  unfold EdwardsPoint.toPoint'
  ext
  · simp [hx_div]
  · simp [hy_div]

end curve25519_dalek.edwards.EdwardsPoint
