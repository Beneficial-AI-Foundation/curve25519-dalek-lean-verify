/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Specs.Field.FieldElement51.IsZero

import Mathlib.Data.Nat.ModEq

/-! # Spec Theorem for `EdwardsPoint::ct_eq`

Specification and proof for `EdwardsPoint::ct_eq`.

This function performs constant-time equality comparison for Edwards points.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field.FieldElement51

namespace curve25519_dalek.edwards.ConstantTimeEqcurve25519_dalekedwardsEdwardsPoint

/-
Natural language description:

    • Compares two EdwardsPoint types to determine whether they represent the same point

    • Checks equality of affine coordinates (x,y) = (X/Z, Y/Z) and (x',y') = (X'/Z', Y'/Z') without
      actually converting to affine coordinates by comparing (X·Z', Y·Z') with (X'·Z, Y'·Z)

    • Crucially does so in constant time irrespective of the inputs to avoid security liabilities

Natural language specs:

    • Requires: Z coordinates must be non-zero mod p (maintained as invariant for valid EdwardsPoints)
    • (e1.X · e2.Z, e1.Y · e2.Z) = (e2.X · e1.Z, e2.Y · e1.Z) ⟺ Choice = True
-/

/-- **Spec and proof concerning `edwards.ConstantTimeEqcurve25519_dalekedwardsEdwardsPoint.ct_eq`**:
- No panic (always returns successfully)
- The result is Choice.one (true) if and only if the two points are equal (mod p) in affine coordinates
-/

@[progress]
theorem ct_eq_spec (e1 e2 : EdwardsPoint)
  -- Bounds are needed for the internal field multiplications
  (h_e1_X : ∀ i, i < 5 → e1.X.val[i]!.val ≤ 2 ^ 53)
  (h_e1_Y : ∀ i, i < 5 → e1.Y.val[i]!.val ≤ 2 ^ 53)
  (h_e1_Z : ∀ i, i < 5 → e1.Z.val[i]!.val ≤ 2 ^ 53)
  (h_e2_X : ∀ i, i < 5 → e2.X.val[i]!.val ≤ 2 ^ 53)
  (h_e2_Y : ∀ i, i < 5 → e2.Y.val[i]!.val ≤ 2 ^ 53)
  (h_e2_Z : ∀ i, i < 5 → e2.Z.val[i]!.val ≤ 2 ^ 53) :
  ∃ c,
  ct_eq e1 e2 = ok c ∧
  (c = Choice.one ↔
    (Field51_as_Nat e1.X * Field51_as_Nat e2.Z) ≡ (Field51_as_Nat e2.X * Field51_as_Nat e1.Z) [MOD p] ∧
    (Field51_as_Nat e1.Y * Field51_as_Nat e2.Z) ≡ (Field51_as_Nat e2.Y * Field51_as_Nat e1.Z) [MOD p]) := by
  unfold ct_eq
  progress as ⟨h1, h2⟩
  · intro i hi; have := h_e1_X i hi; scalar_tac
  · intro i hi; have := h_e2_Z i hi; scalar_tac

  progress as ⟨h3, h4⟩
  · intro i hi; have := h_e2_X i hi; scalar_tac
  · intro i hi; have := h_e1_Z i hi; scalar_tac

  progress as ⟨h5, h6⟩
  progress as ⟨h7, h8⟩
  · intro i hi; have := h_e1_Y i hi; scalar_tac
  · intro i hi; have := h_e2_Z i hi; scalar_tac

  progress as ⟨h9, h10⟩
  · intro i hi; have := h_e2_Y i hi; scalar_tac
  · intro i hi; have := h_e1_Z i hi; scalar_tac

  progress as ⟨h11, h12⟩
  progress as ⟨h13, h14⟩

  simp only [h14, h6, h12]

  -- "Equality of to_bytes results is equivalent to equality modulo p"
  have to_bytes_iff_mod (x y : backend.serial.u64.field.FieldElement51) :
      x.to_bytes = y.to_bytes ↔ Field51_as_Nat x % p = Field51_as_Nat y % p := by
    -- Retrieve the spec for both elements (existence of canonical bytes)
    have ⟨xb, hxb_eq, hxb_mod, hxb_lt⟩ := to_bytes_spec x
    have ⟨yb, hyb_eq, hyb_mod, hyb_lt⟩ := to_bytes_spec y

    rw [hxb_eq, hyb_eq]
    simp only [ok.injEq] -- ok a = ok b ↔ a = b

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

  refine ⟨fun ⟨hx, hy⟩ ↦ ⟨?_, ?_⟩, fun ⟨hx, hy⟩ ↦ ⟨?_, ?_⟩⟩
  · -- Forward X: h1=h3 -> SpecL=SpecR
    exact Nat.ModEq.trans (Nat.ModEq.trans (Nat.ModEq.symm h2) hx) h4
  · -- Forward Y: h7=h9 -> SpecL=SpecR
    exact Nat.ModEq.trans (Nat.ModEq.trans (Nat.ModEq.symm h8) hy) h10
  · -- Backward X: SpecL=SpecR -> h1=h3
    exact Nat.ModEq.trans (Nat.ModEq.trans h2 hx) (Nat.ModEq.symm h4)
  · -- Backward Y: SpecL=SpecR -> h7=h9
    exact Nat.ModEq.trans (Nat.ModEq.trans h8 hy) (Nat.ModEq.symm h10)


end curve25519_dalek.edwards.ConstantTimeEqcurve25519_dalekedwardsEdwardsPoint
