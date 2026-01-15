/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Defs.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg

/-! # Spec Theorem for `ProjectiveNielsPoint::neg`

Specification and proof for `ProjectiveNielsPoint::neg`.

This function implements the negation of a point in projective Niels coordinates.
Given a ProjectiveNielsPoint N = (Y+X, Y−X, Z, 2dXY), it computes -N by:
- Swapping Y_plus_X and Y_minus_X
- Keeping Z unchanged
- Negating T2d

The concrete formulas are:
- Y_plus_X'  = Y_minus_X
- Y_minus_X' = Y_plus_X
- Z'         = Z
- T2d'       = -T2d

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs, lines 503:4-510:5
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.backend.serial.curve_models

namespace curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint

/-
natural language description:

• Takes a ProjectiveNielsPoint (Y+X, Y−X, Z, 2dXY) in projective Niels coordinates
and returns its negation -N = (Y−X, Y+X, Z, −2dXY). Arithmetic is performed in
the field 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Given input N = (Y+X, Y−X, Z, 2dXY), the output -N = (Y_plus_X', Y_minus_X', Z', T2d')
  satisfies modulo p:
  - Y_plus_X' = Y_minus_X (coordinates are swapped)
  - Y_minus_X' = Y_plus_X (coordinates are swapped)
  - Z' = Z (Z coordinate unchanged)
  - T2d' ≡ -T2d (mod p) (T2d coordinate is negated)
-/

/-- **Spec and proof concerning `backend.serial.curve_models.ProjectiveNielsPoint.neg`**:
- No panic (always returns successfully)
- Given input:
  • a ProjectiveNielsPoint `self` with coordinates (Y_plus_X, Y_minus_X, Z, T2d),
the output ProjectiveNielsPoint computed by `neg self` has coordinates
(Y_plus_X', Y_minus_X', Z', T2d') where:
- Y_plus_X' = Y_minus_X (the coordinates are swapped)
- Y_minus_X' = Y_plus_X (the coordinates are swapped)
- Z' = Z (the Z coordinate is unchanged)
- T2d' ≡ -T2d (mod p) (the T2d coordinate is negated modulo p)

where p = 2^255 - 19.

This implements the negation of a point in projective Niels coordinates.
-/
theorem neg_spec
    (self : backend.serial.curve_models.ProjectiveNielsPoint)
    (self_bound : ∀ i < 5, self.T2d[i]!.val < 2 ^ 54) :
    ∃ result, NegShared0ProjectiveNielsPointProjectiveNielsPoint.neg self = ok result ∧
    result.Y_plus_X = self.Y_minus_X ∧
    result.Y_minus_X = self.Y_plus_X ∧
    result.Z = self.Z ∧
    (Field51_as_Nat self.T2d + Field51_as_Nat result.T2d) % p = 0 := by
  unfold NegShared0ProjectiveNielsPointProjectiveNielsPoint.neg
  progress*





end curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint
