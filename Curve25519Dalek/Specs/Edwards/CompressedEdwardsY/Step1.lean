/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI Assistant
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.Specs.Edwards.CompressedEdwardsY.AsBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.EdwardsD
import Curve25519Dalek.Specs.Field.FieldElement51.SqrtRatioi

/-! # Spec Theorem for `CompressedEdwardsY::decompress::step_1`

Specification for the first step of `CompressedEdwardsY::decompress`.

This function performs the initial decompression step which:
1. Extracts the y-coordinate from the compressed representation
2. Computes u = y² - 1
3. Computes v = dy² + 1 where d is the Edwards curve constant
4. Computes the x-coordinate using sqrt_ratio_i(u, v)
5. Returns a validity flag and the coordinates (X, Y, Z)

The twisted Edwards curve equation is: -x² + y² = 1 + d·x²·y²
Rearranging for x²: x² = (y² - 1) / (d·y² + 1)
So u is the numerator and v the denominator of x².

Ported from the Verus spec in dalek-lite/curve25519-dalek/src/edwards.rs (lines 359-392),
which asserts curve-level properties: `is_on_edwards_curve(X, Y)` and
`is_valid_edwards_y_coordinate(Y)`.

**Source**: curve25519-dalek/src/edwards.rs, lines 216-227
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.constants
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.field.FieldElement51
open Edwards

namespace curve25519_dalek.edwards.CompressedEdwardsY

/-
Natural language description:

    - Takes a CompressedEdwardsY (32-byte array) as input
    - Extracts the y-coordinate from the byte array via from_bytes (masks top bit)
    - Sets Z = 1 (projective coordinate)
    - Computes YY = Y²
    - Computes u = YY - Z = y² - 1
    - Computes v = d·YY + Z = d·y² + 1, where d is the Edwards curve constant
    - Computes (is_valid_y_coord, X) = sqrt_ratio_i(u, v)
    - Returns (is_valid_y_coord, X, Y, Z)

Natural language specs (ported from Verus):

    - The function always succeeds (no panic) for any 32-byte input
    - Y encodes the y-coordinate from the input bytes (mod p)
    - Z = 1 (the multiplicative identity)
    - is_valid_y_coord = 1 iff there exists an x such that (x, y) is on the curve
    - If is_valid_y_coord = 1, then (X, Y) is on the twisted Edwards curve
    - X has even parity (non-negative square root)
    - Output bounds: Y limbs < 2^51, Z limbs < 2^51, X limbs ≤ 2^53-1
-/

/-- **Spec for `edwards.decompress.step_1`**. No panic.

Returns a tuple `(is_valid_y_coord, X, Y, Z)` — let `x := X.toField`, `y := Y.toField`.

- `Y` is the field element decoded from the low 255 bits of `cey`:
  `Field51_as_Nat Y ≡ (U8x32_as_Nat cey % 2^255) [MOD p]`, with `Y` limbs `< 2^51`.
- `Z` is the multiplicative identity: `Field51_as_Nat Z = 1`, with `Z` limbs `< 2^51`.
- `X` is the non-negative square root produced by `sqrt_ratio_i`:
  limbs `≤ 2^53 - 1` (inherited from `sqrt_ratio_i_spec'` — see
  `Ed_audit_ref/README.md` DEFER-1), parity `(Field51_as_Nat X % p) % 2 = 0`.
- `is_valid_y_coord.val = 1` iff `y` is a valid Edwards y-coordinate, i.e. there
  exists some `x'` satisfying the twisted Edwards curve equation
  `a·x'^2 + y^2 = 1 + d·x'^2·y^2`.
- When valid, the pair `(x, y)` satisfies that same equation.
-/
@[step]
theorem step_1_spec (cey : edwards.CompressedEdwardsY) :
    edwards.decompress.step_1 cey ⦃ result =>
      let (is_valid_y_coord, X, Y, Z) := result
      let x := X.toField
      let y := Y.toField
      Field51_as_Nat Y ≡ (U8x32_as_Nat cey % 2 ^ 255) [MOD p] ∧
      (∀ i < 5, Y[i]!.val < 2 ^ 51) ∧
      Field51_as_Nat Z = 1 ∧
      (∀ i < 5, Z[i]!.val < 2 ^ 51) ∧
      (∀ i < 5, X[i]!.val ≤ 2 ^ 53 - 1) ∧
      (Field51_as_Nat X % p) % 2 = 0 ∧
      (is_valid_y_coord.val = 1#u8 ↔
        ∃ x' : CurveField, Ed25519.a * x' ^ 2 + y ^ 2 = 1 + Ed25519.d * x' ^ 2 * y ^ 2) ∧
      (is_valid_y_coord.val = 1#u8 →
        Ed25519.a * x ^ 2 + y ^ 2 = 1 + Ed25519.d * x ^ 2 * y ^ 2) ⦄ := by
  unfold edwards.decompress.step_1
  let* ⟨ a, a_post ⟩ ← edwards.CompressedEdwardsY.as_bytes_spec
  let* ⟨ Y, Y_mod, Y_bounds ⟩ ← from_bytes_spec
  let* ⟨ Z, Z_val, Z_bounds ⟩ ← ONE_spec
  let* ⟨ YY, YY_mod, YY_bounds ⟩ ← square_spec
  let* ⟨ u, u_post1, u_post2 ⟩ ← sub_spec
  let* ⟨ fe, fe_post1, fe_post2 ⟩ ← EDWARDS_D_spec
  let* ⟨ fe1, fe1_post1, fe1_post2 ⟩ ← mul_spec
  let* ⟨ v, v_post1, v_post2 ⟩ ← add_spec
  let* ⟨ sqrt_res, X_lbounds, X_parity, sq_case1, sq_case2, sq_case3, sq_case4 ⟩ ←
    sqrt_ratio_i_spec
  -- Discharge the 8 postconditions one by one
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. Field51_as_Nat Y ≡ (U8x32_as_Nat cey % 2^255) [MOD p]
    rw [a_post] at Y_mod
    exact Y_mod
  · -- 2. ∀ i < 5, Y[i]!.val < 2^51
    exact Y_bounds
  · -- 3. Field51_as_Nat Z = 1
    exact Z_val
  · -- 4. ∀ i < 5, Z[i]!.val < 2^51
    exact Z_bounds
  · -- 5. ∀ i < 5, X[i]!.val ≤ 2^53 - 1
    exact X_lbounds
  · -- 6. (Field51_as_Nat X % p) % 2 = 0
    exact X_parity
  · -- 7. is_valid_y_coord.val = 1 ↔ ∃ x' : CurveField, curve_eq(x', y)
    sorry
  · -- 8. is_valid_y_coord.val = 1 → curve_eq(x, y)
    sorry

end curve25519_dalek.edwards.CompressedEdwardsY
