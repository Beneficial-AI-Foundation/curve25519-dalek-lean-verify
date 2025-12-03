/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

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
@[progress]
theorem add_spec
  (self : edwards.EdwardsPoint)
  (other : backend.serial.curve_models.ProjectiveNielsPoint)
  (h_selfX_bounds : ∀ i, i < 5 → (self.X[i]!).val < 2 ^ 54)
  (h_selfY_bounds : ∀ i, i < 5 → (self.Y[i]!).val < 2 ^ 54)
  (h_selfZ_bounds : ∀ i, i < 5 → (self.Z[i]!).val < 2 ^ 54)
  (h_selfT_bounds : ∀ i, i < 5 → (self.T[i]!).val < 2 ^ 54)
  (h_otherYpX_bounds : ∀ i, i < 5 → (other.Y_plus_X[i]!).val < 2 ^ 54)
  (h_otherYmX_bounds : ∀ i, i < 5 → (other.Y_minus_X[i]!).val < 2 ^ 54)
  (h_otherZ_bounds   : ∀ i, i < 5 → (other.Z[i]!).val < 2 ^ 54)
  (h_otherT2d_bounds : ∀ i, i < 5 → (other.T2d[i]!).val < 2 ^ 54) :
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
X' % p = (((Y + X) * YpX) - ((Y - X) * YmX)) % p ∧
Y' % p = (((Y + X) * YpX) + ((Y - X) * YmX)) % p ∧
Z' % p = ((2 * Z * Z₀) + (T * T2d)) % p ∧
T' % p = ((2 * Z * Z₀) - (T * T2d)) % p
:= by
  sorry

end curve25519_dalek.backend.serial.curve_models.CompletedPoint
