/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.AddAssign

/-! # Spec Theorem for `CompletedPoint::add`

Specification and proof for `CompletedPoint::add`.

This function implements the mixed addition of an Edwards point in extended
coordinates with a point in projective Niels coordinates, returning the result
in completed coordinates (ℙ¹ × ℙ¹). Given
- an EdwardsPoint P = (X:Y:Z:T) in extended ℙ³ coordinates (with X/Z = x, Y/Z = y, and T = XY/Z),
- a ProjectiveNielsPoint N = (Y+X, Y−X, Z, 2dXY),
it computes a CompletedPoint C = (X':Y':Z':T') corresponding to P + N.

The concrete formulas are:
- Y_plus_X  = Y + X
- Y_minus_X = Y − X
- PP        = Y_plus_X  · N.Y_plus_X
- MM        = Y_minus_X · N.Y_minus_X
- TT2d      = T · N.T2d
- ZZ        = Z · N.Z
- ZZ2       = ZZ + ZZ
- X'        = PP − MM
- Y'        = PP + MM
- Z'        = ZZ2 + TT2d
- T'        = ZZ2 − TT2d

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAProjectiveNielsPointCompletedPoint
namespace curve25519_dalek.backend.serial.curve_models.CompletedPoint

/-
natural language description:

• Takes an EdwardsPoint (X, Y, Z, T) in extended coordinates and a ProjectiveNielsPoint
(Y+X, Y−X, Z, 2dXY) and returns a CompletedPoint (X', Y', Z', T') in completed coordinates
(ℙ¹ × ℙ¹). Arithmetic is performed in the field 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Given inputs P = (X, Y, Z, T) and N = (Y+X, Y−X, Z, 2dXY), the output C = (X', Y', Z', T')
  satisfies modulo p:
  - X' ≡ ( (Y+X)·N.Y_plus_X − (Y−X)·N.Y_minus_X ) (mod p)
  - Y' ≡ ( (Y+X)·N.Y_plus_X + (Y−X)·N.Y_minus_X ) (mod p)
  - Z' ≡ ( 2·Z·N.Z + T·N.T2d ) (mod p)
  - T' ≡ ( 2·Z·N.Z − T·N.T2d ) (mod p)
-/
/-- **Spec and proof concerning `backend.serial.curve_models.CompletedPoint.add`**:
- No panic (always returns successfully)
- Given inputs:
  • an EdwardsPoint `self` with coordinates (X, Y, Z, T), and
  • a ProjectiveNielsPoint `other` with coordinates (Y_plus_X, Y_minus_X, Z, T2d),
the output CompletedPoint (X', Y', Z', T') computed by `add self other` satisfies modulo p:
- X' ≡ ( (Y+X)·Y_plus_X − (Y−X)·Y_minus_X ) (mod p)
- Y' ≡ ( (Y+X)·Y_plus_X + (Y−X)·Y_minus_X ) (mod p)
- Z' ≡ ( 2·Z·Z_other + T·T2d ) (mod p)
- T' ≡ ( 2·Z·Z_other − T·T2d ) (mod p)
where p = 2^255 - 19
These are the standard mixed-addition formulas via projective Niels coordinates,
returning the result in completed coordinates.
-/

theorem add_assign_spec' (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 54)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) :
    ∃ result, backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign a b = ok result ∧
    (∀ i < 5, (result[i]!).val = (a[i]!).val + (b[i]!).val) ∧
    (∀ i < 5, result[i]!.val < 2 ^ 55) := by
  unfold backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign
  have add_lt: ∀ j < 5, (0#usize).val ≤ j → (a[j]!).val + (b[j]!).val ≤ U64.max := by
    intro i hi hi0
    have :(a[i]!).val + (b[i]!).val < 2 ^ 54 + 2 ^ 52:= by
      have := ha i hi; have := hb i hi; omega
    apply le_trans (le_of_lt this)
    scalar_tac
  obtain ⟨w, hw_ok, hw_eq, hw_lt⟩  := spec_imp_exists (backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop_spec a b 0#usize (by simp) add_lt)
  simp[hw_ok]
  constructor
  · simp_all
  · intro i hi
    have :(a[i]!).val + (b[i]!).val < 2 ^ 54 + 2 ^ 52:= by
      have := ha i hi; have := hb i hi; omega
    simp_all
    apply lt_trans this
    simp

theorem add_spec' {a b : Array U64 5#usize}
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) :
    ∃ result, Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add a b = ok result ∧
    (∀ i < 5, result[i]!.val = a[i]!.val + b[i]!.val) ∧
    (∀ i < 5, result[i]!.val < 2^55) := by
  unfold Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add
  obtain ⟨w, hw_ok, hw, hw0 ⟩:= add_assign_spec' a b ha hb
  simp_all

/-- Tighter add_assign spec: (< 2^52) + (< 2^52) → < 2^53 -/
theorem add_assign_spec_52_52 (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 52)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) :
    ∃ result, backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign a b = ok result ∧
    (∀ i < 5, (result[i]!).val = (a[i]!).val + (b[i]!).val) ∧
    (∀ i < 5, result[i]!.val < 2 ^ 53) := by
  unfold backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign
  have add_lt: ∀ j < 5, (0#usize).val ≤ j → (a[j]!).val + (b[j]!).val ≤ U64.max := by
    intro i hi _
    have : (a[i]!).val + (b[i]!).val < 2 ^ 52 + 2 ^ 52 := by
      have := ha i hi; have := hb i hi; omega
    apply le_trans (le_of_lt this); scalar_tac
  obtain ⟨w, hw_ok, hw_eq, _⟩ := spec_imp_exists (backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop_spec a b 0#usize (by simp) add_lt)
  simp [hw_ok]
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · simpa using hw_eq i hi (by scalar_tac)
  · have h := hw_eq i hi (by scalar_tac)
    have ha' := ha i hi; have hb' := hb i hi
    have hsum : (a[i]!).val + (b[i]!).val < 2 ^ 53 := by omega
    simp_all

/-- Tighter add_assign spec: (< 2^53) + (< 2^52) → < 2^54 -/
theorem add_assign_spec_53_52 (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 53)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) :
    ∃ result, backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign a b = ok result ∧
    (∀ i < 5, (result[i]!).val = (a[i]!).val + (b[i]!).val) ∧
    (∀ i < 5, result[i]!.val < 2 ^ 54) := by
  unfold backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign
  have add_lt: ∀ j < 5, (0#usize).val ≤ j → (a[j]!).val + (b[j]!).val ≤ U64.max := by
    intro i hi _
    have : (a[i]!).val + (b[i]!).val < 2 ^ 53 + 2 ^ 52 := by
      have := ha i hi; have := hb i hi; omega
    apply le_trans (le_of_lt this); scalar_tac
  obtain ⟨w, hw_ok, hw_eq, _⟩ := spec_imp_exists (backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop_spec a b 0#usize (by simp) add_lt)
  simp [hw_ok]
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · simpa using hw_eq i hi (by scalar_tac)
  · have h := hw_eq i hi (by scalar_tac)
    have ha' := ha i hi; have hb' := hb i hi
    have hsum : (a[i]!).val + (b[i]!).val < 2 ^ 54 := by omega
    simp_all

/-- Tighter add spec using Add.add: (< 2^52) + (< 2^52) → < 2^53 -/
theorem add_spec_52_52 {a b : Array U64 5#usize}
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 52) (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) :
    ∃ result, Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add a b = ok result ∧
    (∀ i < 5, result[i]!.val = a[i]!.val + b[i]!.val) ∧
    (∀ i < 5, result[i]!.val < 2^53) := by
  unfold Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add
  obtain ⟨w, hw_ok, hw_eq, hw_bounds⟩ := add_assign_spec_52_52 a b ha hb
  simp_all

/-- Tighter add spec using Add.add: (< 2^53) + (< 2^52) → < 2^54 -/
theorem add_spec_53_52 {a b : Array U64 5#usize}
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 53) (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) :
    ∃ result, Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add a b = ok result ∧
    (∀ i < 5, result[i]!.val = a[i]!.val + b[i]!.val) ∧
    (∀ i < 5, result[i]!.val < 2^54) := by
  unfold Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add
  obtain ⟨w, hw_ok, hw_eq, hw_bounds⟩ := add_assign_spec_53_52 a b ha hb
  simp_all

set_option maxHeartbeats 1000000 in
-- simp_all is heavy
/-- **Auxiliary spec for `add`** proving arithmetic correctness.
Input bounds: EdwardsPoint coords < 2^53, ProjectiveNielsPoint coords < 2^53.
Output: arithmetic relations modulo p with explicit output bounds.

Output bounds (all < 2^54, so output satisfies CompletedPoint.IsValid):
- X (from sub): < 2^52
- Y (from add PP+MM): < 2^53
- Z (from add ZZ2+TT2d): < 2^54 (ZZ2 < 2^53, TT2d < 2^52)
- T (from sub): < 2^52
-/
@[progress]
theorem add_spec_aux
    (self : edwards.EdwardsPoint)
    (other : backend.serial.curve_models.ProjectiveNielsPoint)
    (h_selfX_bounds : ∀ i, i < 5 → (self.X[i]!).val < 2 ^ 53)
    (h_selfY_bounds : ∀ i, i < 5 → (self.Y[i]!).val < 2 ^ 53)
    (h_selfZ_bounds : ∀ i, i < 5 → (self.Z[i]!).val < 2 ^ 53)
    (h_selfT_bounds : ∀ i, i < 5 → (self.T[i]!).val < 2 ^ 53)
    (h_otherYpX_bounds : ∀ i, i < 5 → (other.Y_plus_X[i]!).val < 2 ^ 53)
    (h_otherYmX_bounds : ∀ i, i < 5 → (other.Y_minus_X[i]!).val < 2 ^ 53)
    (h_otherZ_bounds : ∀ i, i < 5 → (other.Z[i]!).val < 2 ^ 53)
    (h_otherT2d_bounds : ∀ i, i < 5 → (other.T2d[i]!).val < 2 ^ 53) :
    add self other ⦃ c =>
    let X := Field51_as_Nat self.X
    let Y := Field51_as_Nat self.Y
    let Z := Field51_as_Nat self.Z
    let T := Field51_as_Nat self.T
    let YpX := Field51_as_Nat other.Y_plus_X
    let YmX := Field51_as_Nat other.Y_minus_X
    let Z₀ := Field51_as_Nat other.Z
    let T2d := Field51_as_Nat other.T2d
    let X' := Field51_as_Nat c.X
    let Y' := Field51_as_Nat c.Y
    let Z' := Field51_as_Nat c.Z
    let T' := Field51_as_Nat c.T
    (X' + Y * YmX) % p = ((Y + X) * YpX + X * YmX) % p ∧
    (Y' + X * YmX) % p = ((Y + X) * YpX + Y  * YmX) % p ∧
    Z' % p = ((2 * Z * Z₀) + (T * T2d)) % p ∧
    (T' + T * T2d) % p = (2 * Z * Z₀ ) % p ∧
    -- Output bounds (all < 2^54)
    (∀ i < 5, c.X[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.Y[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.Z[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.T[i]!.val < 2 ^ 54) ⦄ := by
  unfold add
  progress as ⟨Y_plus_X , h_Y_plus_X, Y_plus_X_bounds ⟩
  progress as ⟨Y_minus_X,   Y_minus_X_bounds, h_Y_minus_X⟩
  · intro i hi
    apply lt_trans (h_selfY_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (h_selfX_bounds i hi)
    simp
  progress  as ⟨ PP , h_PP , PP_bounds⟩
  · intro i hi
    apply lt_trans (h_otherYpX_bounds  i hi)
    simp
  progress  as ⟨ MM, h_MM, MM_bounds⟩
  · intro i hi
    apply lt_trans (Y_minus_X_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (h_otherYmX_bounds i hi)
    simp
  progress  as ⟨ TT2d, h_TT2d, TT2d_bounds⟩
  · intro i hi
    apply lt_trans (h_selfT_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (h_otherT2d_bounds i hi)
    simp
  progress  as ⟨ ZZ, h_ZZ, ZZ_bounds⟩
  · intro i hi
    apply lt_trans (h_selfZ_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (h_otherZ_bounds i hi)
    simp
  progress as ⟨ZZ2, h_ZZ2,  ZZ2_bounds⟩
  · intro i hi
    apply lt_trans (ZZ_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (ZZ_bounds i hi)
    simp
  progress as ⟨fe, h_fe,  fe_bounds⟩
  · intro i hi
    apply lt_trans (PP_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (MM_bounds i hi)
    simp
  -- Use tighter add spec for Y = PP + MM: (< 2^52) + (< 2^52) → < 2^53
  obtain ⟨fe1, h_fe1_ok, h_fe1, fe1_bounds⟩ := add_spec_52_52 PP_bounds MM_bounds
  simp only [h_fe1_ok, bind_tc_ok]
  -- ZZ2 < 2^53 (from add of two < 2^52 values)
  have hzz2_tight : ∀ i < 5, ZZ2[i]!.val < 2 ^ 53 := by
    intro i hi
    have h1 : ZZ2[i]!.val = ZZ[i]!.val + ZZ[i]!.val := h_ZZ2 i hi
    have h2 : ZZ[i]!.val < 2 ^ 52 := ZZ_bounds i hi
    calc ZZ2[i]!.val = ZZ[i]!.val + ZZ[i]!.val := h1
        _ < 2 ^ 52 + 2 ^ 52 := by omega
        _ = 2 ^ 53 := by norm_num
  -- Use tighter add spec: (< 2^53) + (< 2^52) → < 2^54
  obtain ⟨fe2, h_fe2_ok, h_fe2, fe2_bounds⟩ := add_spec_53_52 hzz2_tight TT2d_bounds
  simp only [h_fe2_ok, bind_tc_ok]
  progress as ⟨fe3, h_fe3, fe3_bounds⟩
  · intro i hi
    apply lt_trans (ZZ2_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (TT2d_bounds i hi)
    simp
  constructor
  · rw[← Nat.ModEq]
    rw[← Nat.ModEq] at fe_bounds
    have :  Field51_as_Nat self.Y + Field51_as_Nat self.X =Field51_as_Nat Y_plus_X := by
      simp[Field51_as_Nat, Finset.sum_range_succ ]
      simp_all
      scalar_tac
    rw[this]
    have := Nat.ModEq.mul_right (Field51_as_Nat other.Y_minus_X) h_Y_minus_X
    have := Nat.ModEq.symm (Nat.ModEq.add_left (Field51_as_Nat fe) this)
    rw[add_mul, ← add_assoc] at this
    apply Nat.ModEq.trans this
    apply Nat.ModEq.add_right
    apply  Nat.ModEq.symm
    apply Nat.ModEq.trans (Nat.ModEq.symm h_PP)
    apply Nat.ModEq.trans (Nat.ModEq.symm fe_bounds)
    apply Nat.ModEq.add_left
    exact h_MM
  constructor
  · rw[← Nat.ModEq]
    have :  Field51_as_Nat fe1 = Field51_as_Nat PP + Field51_as_Nat MM := by
      simp[Field51_as_Nat, Finset.sum_range_succ]
      simp_all
      scalar_tac
    rw[this]
    have := Nat.ModEq.add h_PP h_MM
    have := Nat.ModEq.add_right (Field51_as_Nat self.X * Field51_as_Nat other.Y_minus_X) this
    apply Nat.ModEq.trans this
    have :  Field51_as_Nat self.Y + Field51_as_Nat self.X =Field51_as_Nat Y_plus_X := by
      simp[Field51_as_Nat, Finset.sum_range_succ ]
      simp_all
      scalar_tac
    rw[this, add_assoc]
    apply Nat.ModEq.add_left
    rw[← add_mul]
    apply Nat.ModEq.mul_right
    rw[← Nat.ModEq] at h_Y_minus_X
    exact h_Y_minus_X
  constructor
  · rw[← Nat.ModEq]
    have :  Field51_as_Nat fe2 = Field51_as_Nat ZZ2 + Field51_as_Nat TT2d := by
      simp[Field51_as_Nat, Finset.sum_range_succ]
      simp_all
      scalar_tac
    rw[this]
    have :  Field51_as_Nat ZZ2 = Field51_as_Nat ZZ + Field51_as_Nat ZZ := by
      simp[Field51_as_Nat, Finset.sum_range_succ]
      simp_all
      scalar_tac
    simp[this, (by scalar_tac :∀ a, a + a = 2 * a)]
    have := Nat.ModEq.mul_left 2 h_ZZ
    have :=  Nat.ModEq.add_right (Field51_as_Nat TT2d) this
    apply Nat.ModEq.trans this
    rw[mul_assoc]
    apply Nat.ModEq.add_left
    exact h_TT2d
  constructor
  · -- T' modular arithmetic
    rw[← Nat.ModEq]
    rw[← Nat.ModEq] at fe3_bounds
    have :=  Nat.ModEq.add_left  (Field51_as_Nat fe3) h_TT2d
    have := Nat.ModEq.trans (Nat.ModEq.symm this) fe3_bounds
    apply Nat.ModEq.trans this
    have :  Field51_as_Nat ZZ2 = Field51_as_Nat ZZ + Field51_as_Nat ZZ := by
      simp[Field51_as_Nat, Finset.sum_range_succ]
      simp_all
      scalar_tac
    rw[this, (by scalar_tac :∀ a, a + a = 2 * a)]
    have := Nat.ModEq.mul_left 2 h_ZZ
    rw[mul_assoc]
    exact this
  -- Output bounds (all < 2^54)
  constructor
  · -- X bounds: fe from sub gives < 2^52 < 2^54
    intro i hi
    apply lt_trans (h_fe i hi)
    norm_num
  constructor
  · -- Y bounds: fe1 from add_spec_52_52 gives < 2^53 < 2^54
    intro i hi
    apply lt_trans (fe1_bounds i hi)
    norm_num
  constructor
  · -- Z bounds: fe2 from add_spec_53_52 gives < 2^54
    exact fe2_bounds
  · -- T bounds: fe3 from sub gives < 2^52 < 2^54
    intro i hi
    apply lt_trans (h_fe3 i hi)
    norm_num

end curve25519_dalek.backend.serial.curve_models.CompletedPoint

/-! ## High-level spec using validity predicates

This section provides a cleaner interface using IsValid predicates for inputs.
The output CompletedPoint satisfies CompletedPoint.IsValid (all coordinates < 2^54).
-/

namespace curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAProjectiveNielsPointCompletedPoint

open Edwards
open curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.edwards

/--
Auxiliary high-level spec for `add` using validity predicates (bounds only).
The theorem states that adding a bounded EdwardsPoint with a valid ProjectiveNielsPoint:
1. Always succeeds
2. Produces a CompletedPoint with the standard mixed-addition arithmetic relations
3. Output bounds: all coordinates < 2^54
-/
theorem add_spec_bounds
    (self : curve25519_dalek.edwards.EdwardsPoint) (hself : self.IsValid)
    (other : ProjectiveNielsPoint) (hother : other.IsValid) :
    ∃ c, add self other = ok c ∧
    let X := Field51_as_Nat self.X
    let Y := Field51_as_Nat self.Y
    let Z := Field51_as_Nat self.Z
    let T := Field51_as_Nat self.T
    let YpX := Field51_as_Nat other.Y_plus_X
    let YmX := Field51_as_Nat other.Y_minus_X
    let Z₀ := Field51_as_Nat other.Z
    let T2d := Field51_as_Nat other.T2d
    let X' := Field51_as_Nat c.X
    let Y' := Field51_as_Nat c.Y
    let Z' := Field51_as_Nat c.Z
    let T' := Field51_as_Nat c.T
    (X' + Y * YmX) % p = ((Y + X) * YpX + X * YmX) % p ∧
    (Y' + X * YmX) % p = ((Y + X) * YpX + Y * YmX) % p ∧
    Z' % p = ((2 * Z * Z₀) + (T * T2d)) % p ∧
    (T' + T * T2d) % p = (2 * Z * Z₀) % p ∧
    -- Output bounds (all < 2^54)
    (∀ i < 5, c.X[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.Y[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.Z[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.T[i]!.val < 2 ^ 54) := by
  exact spec_imp_exists (CompletedPoint.add_spec_aux self other
    hself.X_bounds hself.Y_bounds hself.Z_bounds hself.T_bounds
    hother.Y_plus_X_bounds hother.Y_minus_X_bounds hother.Z_bounds hother.T2d_bounds)

set_option maxHeartbeats 1600000 in
/-- Spec for `add`.
The theorem states that adding a valid EdwardsPoint with a valid ProjectiveNielsPoint:
1. Always succeeds
2. The output CompletedPoint is valid (bounds and algebraic properties)
3. The output represents the sum of the input points
The mixed addition formulas implement elliptic curve point addition on twisted Edwards curves.
-/
theorem add_spec
    (self : curve25519_dalek.edwards.EdwardsPoint) (hself : self.IsValid)
    (other : ProjectiveNielsPoint) (hother : other.IsValid) :
    ∃ c, add self other = ok c ∧
    c.IsValid ∧ c.toPoint = self.toPoint + other.toPoint := by
  obtain ⟨c, hc_run, hX_arith, hY_arith, hZ_arith, hT_arith, hcX_bounds, hcY_bounds, hcZ_bounds, hcT_bounds⟩ :=
    add_spec_bounds self hself other hother

  use c, hc_run

  -- Lift arithmetic to field equalities
  have hX_F : c.X.toField + self.Y.toField * other.Y_minus_X.toField =
      (self.Y.toField + self.X.toField) * other.Y_plus_X.toField +
      self.X.toField * other.Y_minus_X.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hX_arith
    push_cast at h
    exact h

  have hY_F : c.Y.toField + self.X.toField * other.Y_minus_X.toField =
      (self.Y.toField + self.X.toField) * other.Y_plus_X.toField +
      self.Y.toField * other.Y_minus_X.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hY_arith
    push_cast at h
    exact h

  have hZ_F : c.Z.toField = 2 * self.Z.toField * other.Z.toField +
      self.T.toField * other.T2d.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hZ_arith
    push_cast at h
    exact h

  have hT_F : c.T.toField + self.T.toField * other.T2d.toField =
      2 * self.Z.toField * other.Z.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hT_arith
    push_cast at h
    exact h

  -- Simplify to get direct expressions for c.X and c.Y
  have hX_F' : c.X.toField = (self.Y.toField + self.X.toField) * other.Y_plus_X.toField -
      (self.Y.toField - self.X.toField) * other.Y_minus_X.toField := by
    have := hX_F; linear_combination this

  have hY_F' : c.Y.toField = (self.Y.toField + self.X.toField) * other.Y_plus_X.toField +
      (self.Y.toField - self.X.toField) * other.Y_minus_X.toField := by
    have := hY_F; linear_combination this

  have hT_F' : c.T.toField = 2 * self.Z.toField * other.Z.toField -
      self.T.toField * other.T2d.toField := by
    have := hT_F; linear_combination this

  -- Setup self's affine coordinates
  set X1 := self.X.toField with hX1_def
  set Y1 := self.Y.toField with hY1_def
  set Z1 := self.Z.toField with hZ1_def
  set T1 := self.T.toField with hT1_def

  have hZ1_ne : Z1 ≠ 0 := hself.Z_ne_zero
  have hZ1_2 : Z1^2 ≠ 0 := pow_ne_zero 2 hZ1_ne
  have hZ1_4 : Z1^4 ≠ 0 := pow_ne_zero 4 hZ1_ne

  have h_self_curve : Ed25519.a * X1^2 * Z1^2 + Y1^2 * Z1^2 = Z1^4 + Ed25519.d * X1^2 * Y1^2 :=
    hself.on_curve
  have h_self_T : X1 * Y1 = T1 * Z1 := hself.T_relation

  set x1 := X1 / Z1 with hx1_def
  set y1 := Y1 / Z1 with hy1_def

  have h_P1_on_curve : Ed25519.a * x1^2 + y1^2 = 1 + Ed25519.d * x1^2 * y1^2 := by
    simp only [Ed25519] at h_self_curve ⊢
    simp only [hx1_def, hy1_def, div_pow]
    field_simp [hZ1_2, hZ1_4]
    linear_combination h_self_curve

  let P1 : Point Ed25519 := ⟨x1, y1, h_P1_on_curve⟩

  -- Setup other's affine coordinates from ProjectiveNielsPoint
  set YpX := other.Y_plus_X.toField with hYpX_def
  set YmX := other.Y_minus_X.toField with hYmX_def
  set Z2 := other.Z.toField with hZ2_def
  set T2d := other.T2d.toField with hT2d_def

  have hZ2_ne : Z2 ≠ 0 := hother.Z_ne_zero
  have h2 : (2 : CurveField) ≠ 0 := by decide
  have h2Z2_ne : 2 * Z2 ≠ 0 := mul_ne_zero h2 hZ2_ne
  have h2Z2_2 : (2 * Z2)^2 ≠ 0 := pow_ne_zero 2 h2Z2_ne
  have h2Z2_4 : (2 * Z2)^4 ≠ 0 := pow_ne_zero 4 h2Z2_ne

  set x2 := (YpX - YmX) / (2 * Z2) with hx2_def
  set y2 := (YpX + YmX) / (2 * Z2) with hy2_def

  have h_P2_on_curve : Ed25519.a * x2^2 + y2^2 = 1 + Ed25519.d * x2^2 * y2^2 := by
    have h_other_curve := hother.on_curve
    simp only [Ed25519] at h_other_curve ⊢
    simp only [hx2_def, hy2_def, div_pow]
    field_simp [h2Z2_2, h2Z2_4]
    ring_nf; ring_nf at h_other_curve
    linear_combination h_other_curve

  let P2 : Point Ed25519 := ⟨x2, y2, h_P2_on_curve⟩

  -- Use completeness theorem for denominators
  have h_denoms := Ed25519.denomsNeZero P1 P2
  have h_denom_plus : 1 + Ed25519.d * x1 * x2 * y1 * y2 ≠ 0 := by
    have h := h_denoms.1
    simp only [P1, P2] at h
    convert h using 1

  have h_denom_minus : 1 - Ed25519.d * x1 * x2 * y1 * y2 ≠ 0 := by
    have h := h_denoms.2
    simp only [P1, P2] at h
    convert h using 1

  -- Bounds are already < 2^54 from add_spec_aux, which satisfies IsValid
  have hcX_valid : c.X.IsValid := hcX_bounds
  have hcY_valid : c.Y.IsValid := hcY_bounds
  have hcZ_valid : c.Z.IsValid := hcZ_bounds
  have hcT_valid : c.T.IsValid := hcT_bounds

  -- Use T2d_relation to express T1*T2d in terms of affine coordinates
  have h_T2d_rel := hother.T2d_relation
  -- T2d_relation: 2 * Z2 * T2d = d * (YpX^2 - YmX^2)
  -- YpX^2 - YmX^2 = (YpX - YmX)(YpX + YmX) = (2*Z2*x2)(2*Z2*y2) = 4*Z2^2*x2*y2
  -- So: T2d = 2*d*Z2*x2*y2

  have h_YpX_YmX : YpX^2 - YmX^2 = (YpX - YmX) * (YpX + YmX) := by ring
  have h_factor_x2y2 : (YpX - YmX) * (YpX + YmX) = 4 * Z2^2 * x2 * y2 := by
    simp only [hx2_def, hy2_def]
    field_simp [h2Z2_ne]
    ring

  have h_T2d_expr : T2d = 2 * Ed25519.d * Z2 * x2 * y2 := by
    -- From T2d_relation: 2 * Z2 * T2d = d * (YpX^2 - YmX^2)
    have h_rel : 2 * Z2 * T2d = Ed25519.d * (YpX^2 - YmX^2) := h_T2d_rel
    rw [h_YpX_YmX, h_factor_x2y2] at h_rel
    -- h_rel: 2 * Z2 * T2d = d * 4 * Z2^2 * x2 * y2
    -- Goal: T2d = 2 * d * Z2 * x2 * y2
    have h_simpl : T2d * (2 * Z2) = 2 * Ed25519.d * Z2 * x2 * y2 * (2 * Z2) := by
      linear_combination h_rel
    field_simp [hZ2_ne, h2] at h_simpl
    calc T2d = 2 * Z2 * Ed25519.d * x2 * y2 := h_simpl
      _ = 2 * Ed25519.d * Z2 * x2 * y2 := by ring

  -- Express T1 in terms of affine coordinates using T_relation
  -- From h_self_T: X1 * Y1 = T1 * Z1, so T1 = X1*Y1/Z1 = (X1/Z1)*(Y1/Z1)*Z1 = x1*y1*Z1
  have h_T1_expr : T1 = x1 * y1 * Z1 := by
    simp only [hx1_def, hy1_def]
    field_simp [hZ1_ne]
    -- Goal: T1 * Z1 = X1 * Y1
    linear_combination -h_self_T

  -- Key: T1 * T2d = 2*d*x1*x2*y1*y2*Z1*Z2
  have h_T1_T2d : T1 * T2d = 2 * Ed25519.d * x1 * x2 * y1 * y2 * Z1 * Z2 := by
    rw [h_T1_expr, h_T2d_expr]
    ring

  -- Therefore Z' = 2*Z1*Z2*(1 + d*x1*x2*y1*y2)
  have hZ_factored : c.Z.toField = 2 * Z1 * Z2 * (1 + Ed25519.d * x1 * x2 * y1 * y2) := by
    rw [hZ_F]
    simp only [hZ1_def, hZ2_def, hT1_def, hT2d_def]
    rw [h_T1_T2d]
    ring

  -- And T' = 2*Z1*Z2*(1 - d*x1*x2*y1*y2)
  have hT_factored : c.T.toField = 2 * Z1 * Z2 * (1 - Ed25519.d * x1 * x2 * y1 * y2) := by
    rw [hT_F']
    simp only [hZ1_def, hZ2_def, hT1_def, hT2d_def]
    rw [h_T1_T2d]
    ring

  -- Prove Z' ≠ 0 and T' ≠ 0 using completeness
  have hcZ_ne : c.Z.toField ≠ 0 := by
    rw [hZ_factored]
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    · exact h2
    · exact hZ1_ne
    · exact hZ2_ne
    · exact h_denom_plus

  have hcT_ne : c.T.toField ≠ 0 := by
    rw [hT_factored]
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    · exact h2
    · exact hZ1_ne
    · exact hZ2_ne
    · exact h_denom_minus

  have h_c_on_curve : Ed25519.a * c.X.toField^2 * c.T.toField^2 +
      c.Y.toField^2 * c.Z.toField^2 =
      c.Z.toField^2 * c.T.toField^2 + Ed25519.d * c.X.toField^2 * c.Y.toField^2 := by
    -- Use add_closure_Ed25519: the sum of two points on Ed25519 stays on the curve
    -- The output affine point (X'/Z', Y'/T') satisfies the curve equation
    have h_sum_on_curve := (P1 + P2).on_curve
    -- Derive factored forms for c.X and c.Y
    have hYpX' : YpX = Z2 * (x2 + y2) := by simp only [hx2_def, hy2_def]; field_simp [h2Z2_ne]; ring
    have hYmX' : YmX = Z2 * (y2 - x2) := by simp only [hx2_def, hy2_def]; field_simp [h2Z2_ne]; ring
    have hX1' : X1 = Z1 * x1 := by simp only [hx1_def]; field_simp [hZ1_ne]
    have hY1' : Y1 = Z1 * y1 := by simp only [hy1_def]; field_simp [hZ1_ne]
    have hX_factored' : c.X.toField = 2 * Z1 * Z2 * (x1 * y2 + y1 * x2) := by
      rw [hX_F', hYpX', hYmX', hX1', hY1']; ring
    have hY_factored' : c.Y.toField = 2 * Z1 * Z2 * (y1 * y2 + x1 * x2) := by
      rw [hY_F', hYpX', hYmX', hX1', hY1']; ring
    -- Relate to the sum (P1 + P2)
    have h_sum_x : (P1 + P2).x = (x1 * y2 + y1 * x2) / (1 + Ed25519.d * x1 * x2 * y1 * y2) := by
      rw [add_x]
    have h_sum_y : (P1 + P2).y = (y1 * y2 + x1 * x2) / (1 - Ed25519.d * x1 * x2 * y1 * y2) := by
      rw [add_y]
      simp only [P1, P2, Ed25519]
      congr 1 <;> ring
    -- From hZ_factored and hT_factored: c.X/c.Z = (P1+P2).x and c.Y/c.T = (P1+P2).y
    have h_cx_eq : c.X.toField / c.Z.toField = (P1 + P2).x := by
      rw [hX_factored', hZ_factored, h_sum_x]
      field_simp [h2, hZ1_ne, hZ2_ne, h_denom_plus]
    have h_cy_eq : c.Y.toField / c.T.toField = (P1 + P2).y := by
      rw [hY_factored', hT_factored, h_sum_y]
      field_simp [h2, hZ1_ne, hZ2_ne, h_denom_minus]
    -- Clear denominators from the affine curve equation
    have hcZ2 : c.Z.toField^2 ≠ 0 := pow_ne_zero 2 hcZ_ne
    have hcT2 : c.T.toField^2 ≠ 0 := pow_ne_zero 2 hcT_ne
    simp only [Ed25519] at h_sum_on_curve ⊢
    -- h_sum_on_curve: -1 * (P1+P2).x^2 + (P1+P2).y^2 = 1 + d * (P1+P2).x^2 * (P1+P2).y^2
    have h_key : (Ed25519.a * (P1 + P2).x^2 + (P1 + P2).y^2) = (1 + Ed25519.d * (P1 + P2).x^2 * (P1 + P2).y^2) := by
      simp only [Ed25519]
      exact h_sum_on_curve
    calc Ed25519.a * c.X.toField^2 * c.T.toField^2 + c.Y.toField^2 * c.Z.toField^2
        = (Ed25519.a * (c.X.toField / c.Z.toField)^2 + (c.Y.toField / c.T.toField)^2) *
            c.Z.toField^2 * c.T.toField^2 := by field_simp [hcZ2, hcT2]
      _ = (Ed25519.a * (P1 + P2).x^2 + (P1 + P2).y^2) * c.Z.toField^2 * c.T.toField^2 := by
            rw [h_cx_eq, h_cy_eq]
      _ = (1 + Ed25519.d * (P1 + P2).x^2 * (P1 + P2).y^2) * c.Z.toField^2 * c.T.toField^2 := by
            rw [h_key]
      _ = c.Z.toField^2 * c.T.toField^2 + Ed25519.d * c.X.toField^2 * c.Y.toField^2 := by
            rw [← h_cx_eq, ← h_cy_eq]
            simp only [div_pow]
            field_simp [hcZ2, hcT2]

  constructor
  · exact {
      X_valid := hcX_valid
      Y_valid := hcY_valid
      Z_valid := hcZ_valid
      T_valid := hcT_valid
      Z_ne_zero := hcZ_ne
      T_ne_zero := hcT_ne
      on_curve := h_c_on_curve
    }

  · have h_c_valid : c.IsValid := {
      X_valid := hcX_valid
      Y_valid := hcY_valid
      Z_valid := hcZ_valid
      T_valid := hcT_valid
      Z_ne_zero := hcZ_ne
      T_ne_zero := hcT_ne
      on_curve := h_c_on_curve
    }

    have ⟨h_cx, h_cy⟩ := CompletedPoint.toPoint_of_isValid h_c_valid
    have ⟨h_selfx, h_selfy⟩ := EdwardsPoint.toPoint_of_isValid hself
    have ⟨h_otherx, h_othery⟩ := ProjectiveNielsPoint.toPoint_of_isValid hother

    -- Derive expressions for YpX, YmX in terms of affine coords
    have hYpX' : YpX = Z2 * (x2 + y2) := by
      simp only [hx2_def, hy2_def]
      field_simp [h2Z2_ne]
      ring
    have hYmX' : YmX = Z2 * (y2 - x2) := by
      simp only [hx2_def, hy2_def]
      field_simp [h2Z2_ne]
      ring

    -- Derive expressions for X1, Y1 in terms of affine coords
    have hX1' : X1 = Z1 * x1 := by simp only [hx1_def]; field_simp [hZ1_ne]
    have hY1' : Y1 = Z1 * y1 := by simp only [hy1_def]; field_simp [hZ1_ne]

    -- Derive X' = 2*Z1*Z2*(x1*y2 + y1*x2)
    have hX_factored : c.X.toField = 2 * Z1 * Z2 * (x1 * y2 + y1 * x2) := by
      rw [hX_F', hYpX', hYmX', hX1', hY1']
      ring

    -- Derive Y' = 2*Z1*Z2*(y1*y2 + x1*x2) = 2*Z1*Z2*(y1*y2 - a*x1*x2) since a = -1
    have hY_factored : c.Y.toField = 2 * Z1 * Z2 * (y1 * y2 + x1 * x2) := by
      rw [hY_F', hYpX', hYmX', hX1', hY1']
      ring

    -- Relate self.toPoint to x1, y1
    have h_self_x : self.toPoint.x = x1 := by simp only [h_selfx, hx1_def, hX1_def, hZ1_def]
    have h_self_y : self.toPoint.y = y1 := by simp only [h_selfy, hy1_def, hY1_def, hZ1_def]

    -- Relate other.toPoint to x2, y2
    have h_other_x : other.toPoint.x = x2 := by simp only [h_otherx, hx2_def, hYpX_def, hYmX_def, hZ2_def]
    have h_other_y : other.toPoint.y = y2 := by simp only [h_othery, hy2_def, hYpX_def, hYmX_def, hZ2_def]

    ext
    · -- x coordinate: X'/Z' = (x1*y2 + y1*x2) / (1 + d*x1*x2*y1*y2)
      rw [h_cx, hX_factored, hZ_factored, add_x, h_self_x, h_self_y, h_other_x, h_other_y]
      field_simp [h2, hZ1_ne, hZ2_ne, h_denom_plus]
    · -- y coordinate: Y'/T' = (y1*y2 - a*x1*x2) / (1 - d*x1*x2*y1*y2)
      rw [h_cy, hY_factored, hT_factored, add_y, h_self_x, h_self_y, h_other_x, h_other_y]
      simp only [Ed25519]
      -- Since a = -1, y1*y2 - a*x1*x2 = y1*y2 - (-(x1*x2)) = y1*y2 + x1*x2
      -- Cancel 2*Z1*Z2 from numerator and denominator, then simplify double negation
      field_simp [h2, hZ1_ne, hZ2_ne, h_denom_minus]
      ring

end curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAProjectiveNielsPointCompletedPoint
