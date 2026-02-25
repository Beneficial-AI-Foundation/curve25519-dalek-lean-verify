/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Math.Montgomery.Curve
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square

/-! # differential_add_and_double

Specification for `montgomery::differential_add_and_double`.

This function performs the core step of the Montgomery ladder: simultaneous point doubling
and differential addition. Given projective points P, Q and the u-coordinate of P-Q,
it computes [2]P and P+Q using formulas from Costello-Smith 2017.
The addition part is 'differential' because it uses P-Q to efficiently compute P+Q

**Source**: curve25519-dalek/src/montgomery.rs:L352-L390
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek
open backend.serial.u64.field.FieldElement51
open Montgomery

namespace curve25519_dalek.montgomery


/-- A projective point is valid if its W coordinate is non-zero,
    meaning it represents a finite affine point u = U/W. -/
def ProjectivePoint.IsValid (P : montgomery.ProjectivePoint) : Prop :=
  (Field51_as_Nat P.W : Montgomery.CurveField) ≠ 0

/-
natural language description:

• Given projective points P and Q on the Montgomery curve, plus the u-coordinate of P-Q,
  computes [2]P and P+Q simultaneously. Arithmetic is performed in 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Returns (P', Q') where P' = [2]P and Q' = P+Q
• Constant-time operation using only field arithmetic
-/

/-- **Spec for `montgomery.differential_add_and_double`**:

- No panic (always succeeds)
- Returns (P', Q') representing [2]P and P+Q in projective coordinates
- Correctness is characterized by compatibility with `Montgomery.uDBL` and `Montgomery.uADD`:
  when converted to affine coordinates, the outputs satisfy these high-level point operations
- At the field level, implements Costello-Smith 2017 formulas:
  * P': U' = (U_P + W_P)²·(U_P - W_P)², W' = 4·U_P·W_P·((U_P - W_P)² + c·4·U_P·W_P)
    where c = (A+2)/4 is the Montgomery curve constant
  * Q': U' = 4·(U_P·U_Q - W_P·W_Q)², W' = u(P-Q)·4·(U_P·W_Q - W_P·U_Q)²
- All operations are constant-time field operations
-/
@[progress]
theorem differential_add_and_double_spec
    (P Q : montgomery.ProjectivePoint)
    (affine_PmQ : backend.serial.u64.field.FieldElement51) :
    differential_add_and_double P Q affine_PmQ ⦃ res =>
      let (P', Q') := res

      (∃ (u_P w_P u_Q w_Q u'_P w'_P u'_Q w'_Q u_diff : Montgomery.CurveField),
        u_P = Field51_as_Nat P.U ∧
        w_P = Field51_as_Nat P.W ∧
        u_Q = Field51_as_Nat Q.U ∧
        w_Q = Field51_as_Nat Q.W ∧
        u_diff = Field51_as_Nat affine_PmQ ∧
        u'_P = Field51_as_Nat P'.U ∧
        w'_P = Field51_as_Nat P'.W ∧
        u'_Q = Field51_as_Nat Q'.U ∧
        w'_Q = Field51_as_Nat Q'.W ∧

        -- Mathematical property 1: Doubling (field-level Costello-Smith formula)
        -- Implements the computation that corresponds to Montgomery.uDBL
        (w_P ≠ 0 → w'_P ≠ 0 →
          u'_P = (u_P + w_P)^2 * (u_P - w_P)^2 ∧
          (w'_P = (4 * u_P * w_P) * ((u_P - w_P)^2 +
            Field51_as_Nat backend.serial.u64.constants.APLUS2_OVER_FOUR  * (4 * u_P * w_P)))) ∧

        -- Mathematical property 2: Differential addition (field-level Costello-Smith formula)
        -- Implements the computation that corresponds to Montgomery.uADD
        (w_P ≠ 0 → w_Q ≠ 0 → w'_Q ≠ 0 →
          let v1 := (u_P + w_P) * (u_Q - w_Q)
          let v2 := (u_P - w_P) * (u_Q + w_Q)
          let v3 := v1 + v2
          let v4 := v1 - v2
          u'_Q = v3^2 ∧
          w'_Q = u_diff * v4^2) ∧

        -- Compatibility with high-level point operations:
        -- When the projective coordinates represent valid affine points on the curve,
        -- the outputs satisfy the identities from Montgomery.uDBL and Montgomery.uADD
        (w_P ≠ 0 → w_Q ≠ 0 → w'_P ≠ 0 → w'_Q ≠ 0 →
          ∀ (P_affine Q_affine : Montgomery.Point),
            (P_affine ≠ 0 ∧ P_affine ≠ Montgomery.T_point ∧
             Q_affine ≠ 0 ∧ Q_affine ≠ Montgomery.T_point ∧
             P_affine ≠ Q_affine ∧
             Montgomery.get_u P_affine = u_P / w_P ∧
             Montgomery.get_u Q_affine = u_Q / w_Q ∧
             Montgomery.get_u (P_affine - Q_affine) = u_diff) →
            -- P' corresponds to [2]P_affine (satisfies uDBL identity)
            (4 * (u'_P / w'_P) * Montgomery.get_u P_affine *
              ((Montgomery.get_u P_affine)^2 + Montgomery.Curve25519.A * Montgomery.get_u P_affine + 1) =
             ((Montgomery.get_u P_affine)^2 - 1)^2) ∧
            -- Q' corresponds to P_affine + Q_affine (satisfies uADD identity)
            ((u'_Q / w'_Q) * Montgomery.get_u (P_affine - Q_affine) *
              (Montgomery.get_u P_affine - Montgomery.get_u Q_affine)^2 =
             (Montgomery.get_u P_affine * Montgomery.get_u Q_affine - 1)^2)))
    ⦄ := by
  sorry

end curve25519_dalek.montgomery
