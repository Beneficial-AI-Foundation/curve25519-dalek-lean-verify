/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong, Oliver Butterley
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

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.backend.serial.curve_models
open AddShared0EdwardsPointSharedAProjectiveNielsPointCompletedPoint
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
    ∃ result, AddAssignFieldElement51SharedAFieldElement51.add_assign a b = ok result ∧
    (∀ i < 5, (result[i]!).val = (a[i]!).val + (b[i]!).val) ∧
    (∀ i < 5, result[i]!.val < 2 ^ 55) := by
  sorry

theorem add_spec' {a b : Array U64 5#usize}
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) :
    ∃ result, AddShared0FieldElement51SharedAFieldElement51FieldElement51.add a b = ok result ∧
    (∀ i < 5, result[i]!.val = a[i]!.val + b[i]!.val) ∧
    (∀ i < 5, result[i]!.val < 2^55) := by
  sorry

/-- Tighter add_assign spec: (< 2^52) + (< 2^52) → < 2^53 -/
theorem add_assign_spec_52_52 (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 52)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) :
    ∃ result, AddAssignFieldElement51SharedAFieldElement51.add_assign a b = ok result ∧
    (∀ i < 5, (result[i]!).val = (a[i]!).val + (b[i]!).val) ∧
    (∀ i < 5, result[i]!.val < 2 ^ 53) := by
  sorry

/-- Tighter add_assign spec: (< 2^53) + (< 2^52) → < 2^54 -/
theorem add_assign_spec_53_52 (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 53)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) :
    ∃ result, AddAssignFieldElement51SharedAFieldElement51.add_assign a b = ok result ∧
    (∀ i < 5, (result[i]!).val = (a[i]!).val + (b[i]!).val) ∧
    (∀ i < 5, result[i]!.val < 2 ^ 54) := by
  sorry

/-- Tighter add spec using Add.add: (< 2^52) + (< 2^52) → < 2^53 -/
theorem add_spec_52_52 {a b : Array U64 5#usize}
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 52) (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) :
    ∃ result, AddShared0FieldElement51SharedAFieldElement51FieldElement51.add a b = ok result ∧
    (∀ i < 5, result[i]!.val = a[i]!.val + b[i]!.val) ∧
    (∀ i < 5, result[i]!.val < 2^53) := by
  sorry

/-- Tighter add spec using Add.add: (< 2^53) + (< 2^52) → < 2^54 -/
theorem add_spec_53_52 {a b : Array U64 5#usize}
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 53) (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) :
    ∃ result, AddShared0FieldElement51SharedAFieldElement51FieldElement51.add a b = ok result ∧
    (∀ i < 5, result[i]!.val = a[i]!.val + b[i]!.val) ∧
    (∀ i < 5, result[i]!.val < 2^54) := by
  sorry

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
  sorry

end curve25519_dalek.backend.serial.curve_models.CompletedPoint

/-! ## High-level spec using validity predicates

This section provides a cleaner interface using IsValid predicates for inputs.
The output CompletedPoint satisfies CompletedPoint.IsValid (all coordinates < 2^54).
-/

namespace curve25519_dalek.backend.serial.curve_models.AddShared0EdwardsPointSharedAProjectiveNielsPointCompletedPoint

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
  sorry

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
  sorry

end curve25519_dalek.backend.serial.curve_models.AddShared0EdwardsPointSharedAProjectiveNielsPointCompletedPoint
