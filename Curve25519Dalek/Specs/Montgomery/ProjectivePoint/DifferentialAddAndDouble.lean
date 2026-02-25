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
- Correctness: the u-coordinates of the outputs correspond to point doubling and
  differential addition on the Montgomery curve
- All operations are constant-time field operations

**Mathematical Specification:**
Given projective points P=(U:W) and Q, plus the u-coordinate of (P-Q),
computes P'=(U':W') representing [2]P and Q' representing P+Q.

In Montgomery curve arithmetic, only u-coordinates are needed for the ladder.
The spec states: for any affine points with matching u-coordinates (u_P/w_P, u_Q/w_Q),
the outputs have u-coordinates matching [2]P and P+Q respectively.
-/
@[progress]
theorem differential_add_and_double_spec
    (P Q : montgomery.ProjectivePoint)
    (affine_PmQ : backend.serial.u64.field.FieldElement51) :
    differential_add_and_double P Q affine_PmQ ⦃ res =>
      let (P', Q') := res
      -- Correctness: outputs preserve u-coordinate relationship with [2]P and P+Q
      (Field51_as_Nat P.W ≠ 0 → Field51_as_Nat Q.W ≠ 0 → Field51_as_Nat P'.W ≠ 0 → Field51_as_Nat Q'.W ≠ 0 →
        ∀ (P_affine Q_affine : Montgomery.Point),
          (P_affine ≠ 0 ∧ P_affine ≠ Montgomery.T_point ∧
           Q_affine ≠ 0 ∧ Q_affine ≠ Montgomery.T_point ∧
           P_affine ≠ Q_affine ∧
           Montgomery.get_u P_affine = Field51_as_Nat P.U / Field51_as_Nat P.W ∧
           Montgomery.get_u Q_affine = Field51_as_Nat Q.U / Field51_as_Nat Q.W ∧
           Montgomery.get_u (P_affine - Q_affine) = Field51_as_Nat affine_PmQ) →
          (Field51_as_Nat P'.U / Field51_as_Nat P'.W = Montgomery.get_u (2 • P_affine)) ∧
          (Field51_as_Nat Q'.U / Field51_as_Nat Q'.W = Montgomery.get_u (P_affine + Q_affine)))
    ⦄ := by
  sorry
end curve25519_dalek.montgomery
