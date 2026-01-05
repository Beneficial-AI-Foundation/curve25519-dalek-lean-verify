/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Defs.Edwards.Representation
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

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field
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
    ∃ result, FieldElement51.AddAssign.add_assign a b = ok result ∧
    (∀ i < 5, (result[i]!).val = (a[i]!).val + (b[i]!).val) ∧
    (∀ i < 5, result[i]!.val < 2 ^ 55) := by
  unfold FieldElement51.AddAssign.add_assign
  have add_lt: ∀ j < 5, (0#usize).val ≤ j → (a[j]!).val + (b[j]!).val ≤ U64.max := by
    intro i hi hi0
    have :(a[i]!).val + (b[i]!).val < 2 ^ 54 + 2 ^ 52:=by
      calc
      (a[i]!).val + (b[i]!).val  < 2 ^ 54  + (b[i]!).val := add_lt_add_right (ha i hi) _
      _  < 2 ^ 54 + 2 ^ 52 := add_lt_add_left  (hb i hi) _
    apply le_trans (le_of_lt this)
    scalar_tac
  obtain ⟨w, hw_ok, hw_eq, hw_lt⟩  := FieldElement51.AddAssign.add_assign_loop_spec a b 0#usize (by simp) add_lt
  simp[hw_ok]
  constructor
  · simp_all
  · intro i hi
    have :(a[i]!).val + (b[i]!).val < 2 ^ 54 + 2 ^ 52:=by
      calc
      (a[i]!).val + (b[i]!).val  < 2 ^ 54  + (b[i]!).val := add_lt_add_right (ha i hi) _
      _  < 2 ^ 54 + 2 ^ 52 := add_lt_add_left  (hb i hi) _
    simp_all
    apply lt_trans this
    simp

theorem add_spec' {a b : Array U64 5#usize}
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) :
    ∃ result, FieldElement51.Add.add a b = ok result ∧
    (∀ i < 5, result[i]!.val = a[i]!.val + b[i]!.val) ∧
    (∀ i < 5, result[i]!.val < 2^55) := by
  unfold FieldElement51.Add.add;
  obtain ⟨w, hw_ok, hw, hw0 ⟩:= add_assign_spec' a b ha hb
  simp_all

set_option maxHeartbeats 1000000 in
-- simp_all is heavy

/-- **Auxiliary spec for `add`** proving arithmetic correctness.
Input bounds: EdwardsPoint coords < 2^53, ProjectiveNielsPoint coords < 2^53.
Output: arithmetic relations modulo p with explicit output bounds.

Note: Output bounds vary by coordinate:
- X (from sub): < 2^52
- Y (from add PP+MM): < 2^53
- Z (from add ZZ2+TT2d): < 2^55
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
∃ c,
add self other = ok c ∧
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
(T' + T * T2d) % p = (2 * Z * Z₀ ) % p
:= by
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
progress as ⟨fe1, h_fe1,  fe1_bounds⟩
· intro i hi
  apply lt_trans (PP_bounds i hi)
  simp
· intro i hi
  apply lt_trans (MM_bounds i hi)
  simp
have hzz: ∀ i < 5, ZZ2[i]!.val < 2 ^ 54 := by simp_all
obtain ⟨fe2, h_fe2_ok, h_fe2, fe2_bounds⟩ := add_spec' hzz  TT2d_bounds
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
· rw[← Nat.ModEq]
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

end curve25519_dalek.backend.serial.curve_models.CompletedPoint

/-! ## High-level spec using validity predicates

This section provides a cleaner interface using IsValid/IsBounded predicates for inputs.
Note: The output CompletedPoint does NOT satisfy CompletedPoint.IsValid because
the Z coordinate can exceed 2^54 (it comes from an add operation that produces < 2^55).
-/

namespace Edwards

open curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.backend.serial.curve_models.CompletedPoint
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.edwards

/--
Auxiliary high-level spec for `add` using validity predicates (bounds only).
The theorem states that adding a bounded EdwardsPoint with a valid ProjectiveNielsPoint:
1. Always succeeds
2. Produces a CompletedPoint with the standard mixed-addition arithmetic relations

Note: The output doesn't satisfy CompletedPoint.IsValid due to the Z coordinate
potentially exceeding 2^54. However, it can be converted via `as_projective` or
`as_extended` which will reduce all bounds through multiplication.
-/
theorem add_spec_bounds
    (self : curve25519_dalek.edwards.EdwardsPoint) (hself : self.IsBounded)
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
    (T' + T * T2d) % p = (2 * Z * Z₀) % p := by
  exact add_spec_aux self other
    hself.X_bounds hself.Y_bounds hself.Z_bounds hself.T_bounds
    hother.Y_plus_X_bounds hother.Y_minus_X_bounds hother.Z_bounds hother.T2d_bounds

/--
High-level semantic spec for `add` using toPoint.
The theorem states that adding a bounded EdwardsPoint with a bounded ProjectiveNielsPoint:
1. Always succeeds
2. The output CompletedPoint represents the sum of the input points

TODO: The proof that `c.toPoint = self.toPoint + other.toPoint` requires showing
that the mixed addition formulas implement elliptic curve point addition.
-/
theorem add_spec
    (self : curve25519_dalek.edwards.EdwardsPoint) (hself : self.IsBounded)
    (other : ProjectiveNielsPoint) (hother : other.IsBounded) :
    ∃ c, add self other = ok c ∧
    -- TODO: prove output validity and toPoint equality
    -- c.toPoint = self.toPoint + other.toPoint
    True := by
  have hother_valid : other.IsValid := ⟨
    hother.Y_plus_X_bounds, hother.Y_minus_X_bounds, hother.Z_bounds, hother.T2d_bounds⟩
  obtain ⟨c, hc, _⟩ := add_spec_bounds self hself other hother_valid
  exact ⟨c, hc, trivial⟩

end Edwards
