/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo, Hoang Le Truong
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Montgomery.Curve
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Specs.Field.FieldElement51.IsZero
import Mathlib.Data.Nat.ModEq

/-!
# Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::ct_eq`

Performs a constant-time equality comparison between two `EdwardsPoint` values:

• Determines whether two `EdwardsPoint`s represent the same curve point.
• Checks equality of affine coordinates `(x, y) = (X/Z, Y/Z)` and
  `(x', y') = (X'/Z', Y'/Z')` without converting to affine form, by comparing
  `(X·Z', Y·Z')` against `(X'·Z, Y'·Z)`.
• Runs in constant time independent of the inputs in order to avoid
  timing-side-channel vulnerabilities.

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.edwards.EdwardsPoint.Insts.SubtleConstantTimeEq

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::ct_eq`**
• No panic (always returns successfully)
• The result is `Choice.one` iff the cross-multiplied projective coordinates
  agree mod p: `X·Z' ≡ X'·Z` and `Y·Z' ≡ Y'·Z` (mod p)
• When both points are valid, this is equivalent to `toPoint` equality
-/
@[step]
theorem ct_eq_spec (self other : EdwardsPoint)
    (h_self_X : ∀ i, i < 5 → self.X.val[i]!.val ≤ 2 ^ 53)
    (h_self_Y : ∀ i, i < 5 → self.Y.val[i]!.val ≤ 2 ^ 53)
    (h_self_Z : ∀ i, i < 5 → self.Z.val[i]!.val ≤ 2 ^ 53)
    (h_other_X : ∀ i, i < 5 → other.X.val[i]!.val ≤ 2 ^ 53)
    (h_other_Y : ∀ i, i < 5 → other.Y.val[i]!.val ≤ 2 ^ 53)
    (h_other_Z : ∀ i, i < 5 → other.Z.val[i]!.val ≤ 2 ^ 53) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      (c = Choice.one ↔
        (Field51_as_Nat self.X * Field51_as_Nat other.Z)
          ≡ (Field51_as_Nat other.X * Field51_as_Nat self.Z) [MOD p] ∧
        (Field51_as_Nat self.Y * Field51_as_Nat other.Z)
          ≡ (Field51_as_Nat other.Y * Field51_as_Nat self.Z) [MOD p]) ∧
      (self.IsValid → other.IsValid → (c = Choice.one ↔ self.toPoint = other.toPoint)) ⦄ := by
  unfold ct_eq
  step as ⟨h1, h2⟩
  step as ⟨h3, h4⟩
  step as ⟨h5, h6⟩
  step as ⟨h7, h8⟩
  step as ⟨h9, h10⟩
  step as ⟨h11, h12⟩
  step as ⟨h13, h14⟩
  simp only [h14, h6, h12]
  have to_bytes_iff_mod (x y : backend.serial.u64.field.FieldElement51) :
      x.to_bytes = y.to_bytes ↔ Field51_as_Nat x % p = Field51_as_Nat y % p := by
    have ⟨xb, hxb_eq, hxb_mod, hxb_lt⟩ := spec_imp_exists (to_bytes_spec x)
    have ⟨yb, hyb_eq, hyb_mod, hyb_lt⟩ := spec_imp_exists (to_bytes_spec y)
    rw [hxb_eq, hyb_eq]
    simp only [ok.injEq]
    have h_x_canon : U8x32_as_Nat xb = Field51_as_Nat x % p := by
      rw [←Nat.mod_eq_of_lt hxb_lt, hxb_mod]
    have h_y_canon : U8x32_as_Nat yb = Field51_as_Nat y % p := by
      rw [←Nat.mod_eq_of_lt hyb_lt, hyb_mod]
    constructor
    · -- Forward: Bytes Equal → Integers Equal → Moduli Equal
      intro h_byte_eq
      rw [←h_x_canon, ←h_y_canon, h_byte_eq]
    · -- Backward: Moduli Equal → Integers Equal → Bytes Equal
      intro h_mod_eq
      have h_nat_eq : U8x32_as_Nat xb = U8x32_as_Nat yb := by
        rw [h_x_canon, h_y_canon]; exact h_mod_eq
      apply U8x32_as_Nat_injective; exact h_nat_eq
  rw [to_bytes_iff_mod h1 h3, to_bytes_iff_mod h7 h9]; dsimp only [Nat.ModEq] at *
  refine ⟨⟨fun ⟨hx, hy⟩ ↦ ⟨?_, ?_⟩, fun ⟨hx, hy⟩ ↦ ⟨?_, ?_⟩⟩,
    fun hv1 hv2 => ?_⟩
  · -- Forward X: h1=h3 -> SpecL=SpecR
    exact Nat.ModEq.trans (Nat.ModEq.trans (Nat.ModEq.symm h2) hx) h4
  · -- Forward Y: h7=h9 -> SpecL=SpecR
    exact Nat.ModEq.trans (Nat.ModEq.trans (Nat.ModEq.symm h8) hy) h10
  · -- Backward X: SpecL=SpecR -> h1=h3
    exact Nat.ModEq.trans (Nat.ModEq.trans h2 hx) (Nat.ModEq.symm h4)
  · -- Backward Y: SpecL=SpecR -> h7=h9
    exact Nat.ModEq.trans (Nat.ModEq.trans h8 hy) (Nat.ModEq.symm h10)
  · -- toPoint equivalence (given hv1 : self.IsValid, hv2 : other.IsValid)
    -- Bridge: modular cross-multiplication equalities ↔ toPoint equality
    have mod_iff_toPoint :
        ((Field51_as_Nat self.X * Field51_as_Nat other.Z)
            ≡ (Field51_as_Nat other.X * Field51_as_Nat self.Z) [MOD p] ∧
         (Field51_as_Nat self.Y * Field51_as_Nat other.Z)
            ≡ (Field51_as_Nat other.Y * Field51_as_Nat self.Z) [MOD p]) ↔
        self.toPoint = other.toPoint := by
      simp only [Montgomery.lift_mod_eq_iff, Nat.cast_mul]
      unfold EdwardsPoint.toPoint
      simp only [hv1, ↓reduceDIte, hv2]
      simp only [EdwardsPoint.toPoint', Edwards.Point.mk.injEq]
      unfold toField
      have hz1 := hv1.Z_ne_zero; unfold toField at hz1
      have hz2 := hv2.Z_ne_zero; unfold toField at hz2
      field_simp
    constructor
    · intro ⟨hx, hy⟩
      exact mod_iff_toPoint.mp ⟨
        Nat.ModEq.trans (Nat.ModEq.trans (Nat.ModEq.symm h2) hx) h4,
        Nat.ModEq.trans (Nat.ModEq.trans (Nat.ModEq.symm h8) hy) h10⟩
    · intro htp
      have ⟨hmx, hmy⟩ := mod_iff_toPoint.mpr htp
      exact ⟨Nat.ModEq.trans (Nat.ModEq.trans h2 hmx) (Nat.ModEq.symm h4),
             Nat.ModEq.trans (Nat.ModEq.trans h8 hmy) (Nat.ModEq.symm h10)⟩

end curve25519_dalek.edwards.EdwardsPoint.Insts.SubtleConstantTimeEq
