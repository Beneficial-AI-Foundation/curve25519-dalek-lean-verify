/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Montgomery.Curve
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes

import Mathlib.Data.Nat.ModEq

/-! # Spec Theorem for `AffinePoint::ct_eq`

Specification and proof for `AffinePoint::ct_eq`.

This function performs constant-time equality comparison for affine Edwards points.
Unlike `EdwardsPoint::ct_eq`, which must cross-multiply by Z coordinates, affine points
store (x, y) directly, so equality reduces to coordinate-wise comparison via
`FieldElement51::ct_eq` on x and y, combined with a bitwise AND.

**Source**: curve25519-dalek/src/edwards/affine.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51

namespace curve25519_dalek.edwards.affine.AffinePoint.Insts.SubtleConstantTimeEq

/-
Natural language description:

    • Compares two AffinePoint types to determine whether they represent the same point

    • Checks equality of coordinates (x, y) by comparing the canonical byte encodings
      of each coordinate via FieldElement51::ct_eq

    • The results for x and y are combined with a bitwise AND on Choice values

    • Crucially does so in constant time irrespective of the inputs to avoid security liabilities

Natural language specs:

    • The operation never panics (always returns successfully)
    • Returns Choice.one (true) if and only if x₁ ≡ x₂ (mod p) and y₁ ≡ y₂ (mod p)
    • When both points are valid, this is equivalent to toPoint equality
-/

/-- **Spec and proof** concerning:
`edwards.affine.AffinePoint.Insts.SubtleConstantTimeEq.ct_eq`:
- No panic (always returns successfully)
- The result is Choice.one (true) if and only if the two points are equal (mod p) in coordinates
- When both points are valid, this is equivalent to toPoint equality
-/
@[step]
theorem ct_eq_spec (self other : AffinePoint) :
  ct_eq self other ⦃ c =>
  (c = Choice.one ↔
    (Field51_as_Nat self.x) ≡ (Field51_as_Nat other.x) [MOD p] ∧
    (Field51_as_Nat self.y) ≡ (Field51_as_Nat other.y) [MOD p]) ∧
  (self.IsValid → other.IsValid → (c = Choice.one ↔ self.toPoint = other.toPoint)) ⦄ := by
  unfold ct_eq
  step as ⟨_, hcx⟩
  step as ⟨_, hcy⟩
  step as ⟨_, hc⟩
  -- hcx : cx = Choice.one ↔ self.x.to_bytes = other.x.to_bytes
  -- hcy : cy = Choice.one ↔ self.y.to_bytes = other.y.to_bytes
  -- hc  : c = Choice.one ↔ cx = Choice.one ∧ cy = Choice.one
  -- Bridge: to_bytes equality ↔ modular equality
  have to_bytes_iff_mod (a b : backend.serial.u64.field.FieldElement51) :
      a.to_bytes = b.to_bytes ↔ Field51_as_Nat a % p = Field51_as_Nat b % p := by
    have ⟨ab, hab_eq, hab_mod, hab_lt⟩ := spec_imp_exists (to_bytes_spec a)
    have ⟨bb, hbb_eq, hbb_mod, hbb_lt⟩ := spec_imp_exists (to_bytes_spec b)
    rw [hab_eq, hbb_eq]
    simp only [ok.injEq]
    have h_a_canon : U8x32_as_Nat ab = Field51_as_Nat a % p := by
      rw [←Nat.mod_eq_of_lt hab_lt, hab_mod]
    have h_b_canon : U8x32_as_Nat bb = Field51_as_Nat b % p := by
      rw [←Nat.mod_eq_of_lt hbb_lt, hbb_mod]
    constructor
    · -- Forward: Bytes Equal → Integers Equal → Moduli Equal
      intro h_byte_eq
      rw [←h_a_canon, ←h_b_canon, h_byte_eq]
    · -- Backward: Moduli Equal → Integers Equal → Bytes Equal
      intro h_mod_eq
      have h_nat_eq : U8x32_as_Nat ab = U8x32_as_Nat bb := by
        rw [h_a_canon, h_b_canon]; exact h_mod_eq
      apply U8x32_as_Nat_injective; exact h_nat_eq
  rw [hc, hcx, hcy, to_bytes_iff_mod, to_bytes_iff_mod]; dsimp only [Nat.ModEq] at *
  refine ⟨Iff.rfl, fun hv1 hv2 => ?_⟩
  -- Bridge: modular coordinate equalities ↔ toPoint equality
  have mod_iff_toPoint :
      ((Field51_as_Nat self.x) ≡ (Field51_as_Nat other.x) [MOD p] ∧
       (Field51_as_Nat self.y) ≡ (Field51_as_Nat other.y) [MOD p]) ↔
      self.toPoint = other.toPoint := by
    simp only [Montgomery.lift_mod_eq_iff]
    unfold AffinePoint.toPoint
    simp only [hv1, ↓reduceDIte, hv2]
    simp only [Edwards.Point.mk.injEq]
    unfold toField; exact Iff.rfl
  exact mod_iff_toPoint

end curve25519_dalek.edwards.affine.AffinePoint.Insts.SubtleConstantTimeEq
