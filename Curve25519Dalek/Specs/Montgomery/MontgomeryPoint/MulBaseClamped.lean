/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.MulBase
import Curve25519Dalek.Specs.Scalar.ClampInteger
/-! # Spec Theorem for `MontgomeryPoint::mul_base_clamped`

Specification and proof for
`curve25519_dalek::montgomery::{curve25519_dalek::montgomery::MontgomeryPoint}::mul_base_clamped`.

This function performs scalar multiplication by the Montgomery basepoint after
clamping the input bytes to a valid scalar, delegating to `MontgomeryPoint.mul_base`.

**Source**: curve25519-dalek/src/montgomery.rs, lines 150:4-158:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64
open Montgomery
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-
natural language description:

• Clamps the 32-byte input to a valid scalar using `scalar.clamp_integer`.

• Computes the Montgomery basepoint multiplication with the clamped scalar by
  delegating to `MontgomeryPoint.mul_base`.

natural language specs:

• The function always succeeds (no panic)
• The result is the Montgomery basepoint multiplication of the clamped scalar
-/

/-
**Spec and proof concerning `montgomery.MontgomeryPoint.mul_base_clamped`**:
- No panic (always returns successfully)
- Clamps input bytes with `scalar.clamp_integer`
- Delegates to `montgomery.MontgomeryPoint.mul_base` with the clamped scalar
- The returned MontgomeryPoint matches the basepoint multiplication result
-/

@[step]
theorem mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ result =>
    (∃ clamped_scalar_nat,
    h ∣ clamped_scalar_nat ∧
    clamped_scalar_nat < 2 ^ 255 ∧
    2 ^ 254 ≤ clamped_scalar_nat ∧
    (if (clamped_scalar_nat • Edwards.basepoint).y = 1 then
        MontgomeryPoint.mkPoint result = T_point
      else MontgomeryPoint.mkPoint result =
        abs_montgomery (clamped_scalar_nat • fromEdwards _root_.Edwards.basepoint))) ⦄ := by
  unfold mul_base_clamped
  step with scalar.clamp_integer_spec'
  step with mul_base_spec
  have :=U8x32_as_Nat_eq_foldr' a
  use U8x32_as_Nat_foldr a
  simp_all

end curve25519_dalek.montgomery.MontgomeryPoint
