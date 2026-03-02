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

/-- A valid Montgomery ladder state: P and Q are projective points, and affine_PmQ
    contains the u-coordinate of the difference (P-Q).

    This captures the invariant maintained by the Montgomery ladder algorithm:
    - The two points P and Q are distinct (P ≠ Q)
    - The difference between them is always known and non-zero
    - This allows the differential addition formula to work correctly
      (the formula requires P ≠ Q to avoid division by zero in (u_P - u_Q))
-/
def valid_ladder_state
    (P Q : montgomery.ProjectivePoint)
    (affine_PmQ : backend.serial.u64.field.FieldElement51) : Prop :=
  ∃ (P_affine Q_affine : Montgomery.Point),
    P_affine ≠ 0 ∧ P_affine ≠ Montgomery.T_point ∧
    Q_affine ≠ 0 ∧ Q_affine ≠ Montgomery.T_point ∧
    P_affine ≠ Q_affine ∧
    Montgomery.get_u P_affine = Field51_as_Nat P.U / Field51_as_Nat P.W ∧
    Montgomery.get_u Q_affine = Field51_as_Nat Q.U / Field51_as_Nat Q.W ∧
    Montgomery.get_u (P_affine - Q_affine) = Field51_as_Nat affine_PmQ ∧
    -- P_affine ∈ Curve25519Dalek.Set ∧
    -- Q_affine ∈ Curve25519Dalek.toSet ∧
    -- (Field51_as_Nat affine_PmQ : Montgomery.CurveField) ≠ 0
    -- 新增：P 和 Q 的 W 坐标的特定代数性质
    -- 保证 doubling 和 differential addition 的分母非零?need?
    (4 : Montgomery.CurveField) * (Field51_as_Nat P.U : Montgomery.CurveField) *
      (Field51_as_Nat P.W : Montgomery.CurveField) *
      ((Field51_as_Nat backend.serial.u64.constants.APLUS2_OVER_FOUR : Montgomery.CurveField) *
        4 * (Field51_as_Nat P.U) * (Field51_as_Nat P.W) +
        ((Field51_as_Nat P.U - Field51_as_Nat P.W) : Montgomery.CurveField)^2) ≠ 0



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

- No panic (always succeeds for valid inputs)
- Requires: P and Q are valid projective points (W ≠ 0)
- Requires: (P, Q, affine_PmQ) form a valid ladder state
  (i.e., affine_PmQ contains the u-coordinate of P-Q)
- Returns (P', Q') representing [2]P and P+Q in projective coordinates
- Ensures: outputs P' and Q' are also valid projective points
- Correctness: the u-coordinates of the outputs correspond to point doubling and
  differential addition on the Montgomery curve
- All operations are constant-time field operations

**Mathematical Specification:**
Given valid projective points P=(U:W) and Q, plus the u-coordinate of (P-Q),
computes P'=(U':W') representing [2]P and Q' representing P+Q.

In Montgomery curve arithmetic, only u-coordinates are needed for the ladder.
The Montgomery ladder invariant maintains that the difference Q-P is known.
-/
@[progress]
theorem differential_add_and_double_spec
    (P Q : montgomery.ProjectivePoint)
    (affine_PmQ : backend.serial.u64.field.FieldElement51)
    (hP_valid : P.IsValid)
    (hQ_valid : Q.IsValid)
    (h_ladder_state : valid_ladder_state P Q affine_PmQ) :
    differential_add_and_double P Q affine_PmQ ⦃ res =>
      let (P', Q') := res
      P'.IsValid ∧ Q'.IsValid ∧
      (∀ (P_affine Q_affine : Montgomery.Point),
        (Montgomery.get_u P_affine = Field51_as_Nat P.U / Field51_as_Nat P.W ∧
         Montgomery.get_u Q_affine = Field51_as_Nat Q.U / Field51_as_Nat Q.W ∧
         Montgomery.get_u (P_affine - Q_affine) = Field51_as_Nat affine_PmQ) →
        (Field51_as_Nat P'.U / Field51_as_Nat P'.W = Montgomery.get_u (2 • P_affine)) ∧
        (Field51_as_Nat Q'.U / Field51_as_Nat Q'.W = Montgomery.get_u (P_affine + Q_affine)))
    ⦄ := by
  -- Unfold the function definition
  unfold differential_add_and_double
  progress* <;> try grind only
  · exact APLUS2_OVER_FOUR_bounded
  · constructor
    -- refine ⟨?h_valid1, ?h_rest⟩
    · unfold  valid_ladder_state at h_ladder_state
      sorry
    · sorry


  -- STEP 1: Execute the computation and extract intermediate values
  -- The function computes 18 intermediate values t0...t17
  -- Following the implementation in Funs.lean:5528-5574

  -- For now, we use a simplified proof structure
  -- TODO: Fill in the detailed computation steps
end curve25519_dalek.montgomery
