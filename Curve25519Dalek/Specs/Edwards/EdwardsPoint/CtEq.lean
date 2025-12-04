/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul

/-! # Spec Theorem for `EdwardsPoint::ct_eq`

Specification and proof for `EdwardsPoint::ct_eq`.

This function performs constant-time equality comparison for Edwards points.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result
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

/- This lemma is also present in IsZero and IsNegative. TODO: refactor to a single source file
to be imported in all needed places-/
lemma choice_val_eq_one_iff (c : subtle.Choice) :
  c.val = 1#u8 ↔ c = Choice.one := by
  cases c with
  | mk v hv =>
    simp [Choice.one]


theorem field_ct_eq_spec (x y : backend.serial.u64.field.FieldElement51)
    (hx : ∀ i < 5, x.val[i]!.val < 2 ^ 54)
    (hy : ∀ i < 5, y.val[i]!.val < 2 ^ 54) :
    ∃ c,
      field.ConstantTimeEqcurve25519_dalekbackendserialu64fieldFieldElement51.ct_eq x y = ok c ∧
      (c.val = 1#u8 ↔ Field51_as_Nat x % p = Field51_as_Nat y % p) := by
  sorry


@[progress]
theorem ct_eq_spec (e1 e2 : EdwardsPoint)
    (h_Z1_nonzero : Field51_as_Nat e1.Z % p ≠ 0)
    (h_Z2_nonzero : Field51_as_Nat e2.Z % p ≠ 0)
    -- Bounds for e1 (Input 1)
    (h_e1_X : ∀ i, i < 5 → e1.X.val[i]!.val ≤ 2 ^ 53)
    (h_e1_Y : ∀ i, i < 5 → e1.Y.val[i]!.val ≤ 2 ^ 53)
    (h_e1_Z : ∀ i, i < 5 → e1.Z.val[i]!.val ≤ 2 ^ 53)
    -- Bounds for e2 (Input 2)
    (h_e2_X : ∀ i, i < 5 → e2.X.val[i]!.val ≤ 2 ^ 53)
    (h_e2_Y : ∀ i, i < 5 → e2.Y.val[i]!.val ≤ 2 ^ 53)
    (h_e2_Z : ∀ i, i < 5 → e2.Z.val[i]!.val ≤ 2 ^ 53) :
    ∃ c,
      ct_eq e1 e2 = ok c ∧
      (c.val = 1#u8 ↔
        (Field51_as_Nat e1.X * Field51_as_Nat e2.Z) ≡ (Field51_as_Nat e2.X * Field51_as_Nat e1.Z) [MOD p] ∧
        (Field51_as_Nat e1.Y * Field51_as_Nat e2.Z) ≡ (Field51_as_Nat e2.Y * Field51_as_Nat e1.Z) [MOD p]) := by
  unfold ct_eq
  progress*

  -- Bounds
  · intro i hi; have := h_e1_X i hi; scalar_tac
  · intro i hi; have := h_e2_Z i hi; scalar_tac
  · intro i hi; have := h_e2_X i hi; scalar_tac
  · intro i hi; have := h_e1_Z i hi; scalar_tac


  progress with field_ct_eq_spec

  · intro i hi; have := fe_post_2 i hi; scalar_tac
  · intro i hi; have := fe1_post_2 i hi; scalar_tac

  progress

  · intro i hi; have := h_e1_Y i hi; scalar_tac
  · intro i hi; have := h_e2_Z i hi; scalar_tac

  progress*

  · intro i hi; have := h_e2_Y i hi; scalar_tac
  · intro i hi; have := h_e1_Z i hi; scalar_tac

  progress with field_ct_eq_spec
  · intro i hi;
    rename_i _ _ fe2 _ h_fe2_bounds

    sorry
  · intro i hi; have := fe3_post_2 i hi; scalar_tac

  sorry

end curve25519_dalek.edwards.ConstantTimeEqcurve25519_dalekedwardsEdwardsPoint
