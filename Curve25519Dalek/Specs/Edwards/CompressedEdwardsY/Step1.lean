/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI Assistant
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
/-! # Spec Theorem for `CompressedEdwardsY::decompress::step_1`

Specification and proof for the first step of `CompressedEdwardsY::decompress`.

This function performs the initial decompression step which:
1. Extracts the y-coordinate from the compressed representation
2. Computes u = y² - 1
3. Computes v = dy² + 1 where d is the Edwards curve constant
4. Computes the x-coordinate using sqrt_ratio_i(u, v)
5. Returns a validity flag and the coordinates (X, Y, Z)

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.constants
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51
open curve25519_dalek.backend.serial.u64.field.SubShared0FieldElement51SharedAFieldElement51FieldElement51
open curve25519_dalek.backend.serial.u64.field.AddShared0FieldElement51SharedAFieldElement51FieldElement51
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.field.FieldElement51
namespace curve25519_dalek.edwards.CompressedEdwardsY

/-
Natural language description:

    - Takes a CompressedEdwardsY (32-byte array) as input
    - Extracts the y-coordinate from the byte array
    - Sets Z = 1 (projective coordinate)
    - Computes YY = Y²
    - Computes u = y² - 1
    - Computes v = dy² + 1, where d is the Edwards curve constant
    - Computes (is_valid_y_coord, X) = sqrt_ratio_i(u, v)
    - Returns (is_valid_y_coord, X, Y, Z)

Natural language specs:

    - The function always succeeds (no panic)
    - Returns a tuple of (is_valid_y_coord, X, Y, Z) where:
      - is_valid_y_coord indicates whether the y-coordinate is valid for the curve
      - X is the computed x-coordinate (may need sign adjustment)
      - Y is the y-coordinate extracted from the input
      - Z = 1 (the projective Z coordinate)
    - Y equals the field element constructed from the input byte array
    - Z equals the multiplicative identity (ONE)
    - u = Y² - 1 (mod p)
    - v = dY² + 1 (mod p), where d is the Edwards curve constant
    - (is_valid_y_coord, X) satisfies the sqrt_ratio_i specification for inputs (u, v)
-/

/-- **Spec for `edwards.CompressedEdwardsY.decompress.step_1`**:
- No panic (always returns successfully)
- Returns a tuple (is_valid_y_coord, X, Y, Z) where:
  - Y is the field element extracted from the compressed representation
  - Z = 1 (the multiplicative identity in the field)
  - u = Y² - 1 (mod p)
  - v = dY² + 1 (mod p), where d is the Edwards curve constant EDWARDS_D
  - (is_valid_y_coord, X) is the result of sqrt_ratio_i(u, v)
  - If is_valid_y_coord is true, then X² * v = u (mod p) or X² * v = -u (mod p)
-/
@[progress]
theorem step_1_spec (cey : edwards.CompressedEdwardsY)
  (bytes : Aeneas.Std.Array U8 32#usize)
  (h_byter : cey.as_bytes = ok bytes) :
    ∃ result, edwards.decompress.step_1 cey = ok result ∧

      let (is_valid_y_coord, X, Y, Z) := result

      -- Z is always ONE
      Z = ONE ∧

      -- Y is extracted from the input bytes
      (from_bytes bytes = ok Y) ∧

      -- The computation follows the curve equation
      (∃ YY u v fe,
        square Y = ok YY ∧
        sub YY ONE = ok u ∧
        mul YY EDWARDS_D = ok fe ∧
        add fe ONE = ok v ∧
        sqrt_ratio_i u v = ok (is_valid_y_coord, X)) := by
  sorry

end curve25519_dalek.edwards.CompressedEdwardsY
