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
Here, differential addition denotes that we uses P-Q to more efficiently compute P+Q.

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
• Implements Costello-Smith 2017 differential formulas (Algorithm 8)
• Constant-time operation using only field arithmetic
-/

/-- **Spec for `montgomery.differential_add_and_double`**:

- No panic (always succeeds)
- Returns (P', Q') representing [2]P and P+Q in projective coordinates
- P' satisfies the doubling formula: U' = (U_P + W_P)²·(U_P - W_P)², W' = 4·U_P·W_P·((U_P - W_P)² + c·4·U_P·W_P)
- Q' satisfies the differential addition formula using u(P-Q) = affine_PmQ:
  U' = 4·(U_P·U_Q - W_P·W_Q)², W' = u(P-Q)·4·(U_P·W_Q - W_P·U_Q)²
- All operations are constant-time field operations
-/
@[progress]
theorem differential_add_and_double_spec
    (P Q : montgomery.ProjectivePoint)
    (affine_PmQ : backend.serial.u64.field.FieldElement51) :
    differential_add_and_double P Q affine_PmQ ⦃ res =>
      let (P', Q') := res

      -- Core property: Computation succeeds and returns valid field elements
      (∃ (u_P w_P u_Q w_Q u'_P w'_P u'_Q w'_Q u_diff : Montgomery.CurveField),
        -- Input coordinates as field elements
        u_P = Field51_as_Nat P.U ∧
        w_P = Field51_as_Nat P.W ∧
        u_Q = Field51_as_Nat Q.U ∧
        w_Q = Field51_as_Nat Q.W ∧
        u_diff = Field51_as_Nat affine_PmQ ∧

        -- Output coordinates as field elements
        u'_P = Field51_as_Nat P'.U ∧
        w'_P = Field51_as_Nat P'.W ∧
        u'_Q = Field51_as_Nat Q'.U ∧
        w'_Q = Field51_as_Nat Q'.W ∧

        -- Mathematical property 1: Doubling formula (from Costello-Smith 2017)
        -- When w_P ≠ 0 and w'_P ≠ 0, the output P' represents [2]P:
        -- The projective coordinates satisfy the doubling identity
        (w_P ≠ 0 → w'_P ≠ 0 →
          -- The doubling formula: relates projective coordinates of P to [2]P
          -- This is compatible with Montgomery.uDBL when converted to affine form
          let u_P_affine := u_P / w_P
          let u_2P_affine := u'_P / w'_P
          -- Costello-Smith doubling formula in projective form:
          -- U_{2P} = (U_P + W_P)²·(U_P - W_P)²
          -- W_{2P} = 4·U_P·W_P·((U_P - W_P)² + ((A+2)/4)·4·U_P·W_P)
          u'_P = (u_P + w_P)^2 * (u_P - w_P)^2 ∧
          (∃ (aplus2_over_four : Montgomery.CurveField),
            aplus2_over_four = Field51_as_Nat backend.serial.u64.constants.APLUS2_OVER_FOUR ∧
            w'_P = (4 * u_P * w_P) * ((u_P - w_P)^2 + aplus2_over_four * (4 * u_P * w_P)))) ∧

        -- Mathematical property 2: Differential addition formula
        -- When w_P ≠ 0, w_Q ≠ 0, and w'_Q ≠ 0, the output Q' represents P+Q:
        -- Given the u-coordinate of P-Q (affine_PmQ), we can compute P+Q
        (w_P ≠ 0 → w_Q ≠ 0 → w'_Q ≠ 0 →
          -- Costello-Smith differential addition formula in projective form:
          -- U_{P+Q} = ((U_P·U_Q - W_P·W_Q))²  (times a constant factor)
          -- W_{P+Q} = u(P-Q)·(U_P·W_Q - W_P·U_Q)²  (times a constant factor)
          let v1 := (u_P + w_P) * (u_Q - w_Q)  -- (U_P + W_P)(U_Q - W_Q)
          let v2 := (u_P - w_P) * (u_Q + w_Q)  -- (U_P - W_P)(U_Q + W_Q)
          let v3 := v1 + v2  -- 2(U_P·U_Q - W_P·W_Q)
          let v4 := v1 - v2  -- 2(U_P·W_Q - W_P·U_Q)
          u'_Q = v3^2 ∧  -- 4(U_P·U_Q - W_P·W_Q)²
          w'_Q = u_diff * v4^2))  -- u(P-Q)·4(U_P·W_Q - W_P·U_Q)²
    ⦄ := by
  sorry

end curve25519_dalek.montgomery
