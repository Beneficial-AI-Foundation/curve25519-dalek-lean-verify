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

This function performs the double-and-add step of the Montgomery ladder algorithm,
which is the core operation for constant-time scalar multiplication on Montgomery curves.

Given projective points P and Q on the Montgomery curve, and the affine u-coordinate
of their difference P-Q, it simultaneously computes:
- [2]P (the doubling of P)
- P+Q (the addition of P and Q)

This operation is fundamental to the Montgomery ladder (Algorithm 8 from Costello-Smith 2017),
which maintains the invariant that two points differ by a known value throughout scalar
multiplication.

**Source**: curve25519-dalek/src/montgomery.rs:L352-L390

### What is "Differential" Addition?

**The term "differential" refers to using the difference (differential) P-Q to compute the sum P+Q.**

In standard elliptic curve addition, to compute P+Q, you only need the coordinates of P and Q.
However, on Montgomery curves, there's a more efficient formula:

**Differential Addition Formula:**
To compute P+Q, you need:
1. The coordinates of P (as projective point U_P:W_P)
2. The coordinates of Q (as projective point U_Q:W_Q)
3. The u-coordinate of their **difference** P-Q (this is the "differential" part!)

The key insight is that you only need the u-coordinate of P-Q, not both u and v coordinates.

**Why is this called "differential"?**
- Because we use the **difference** (P-Q) to help compute the **sum** (P+Q)
- The term "differential" emphasizes that we're working with differences between points
- This is contrast to standard addition formulas that don't require difference information


## Algorithm

The function implements formulas from Costello-Smith 2017, Section 3.2:

For doubling [2]P:
- U₂ = (U_P + W_P)² · (U_P - W_P)²
- W₂ = 4·U_P·W_P · ((U_P - W_P)² + ((A+2)/4)·4·U_P·W_P)

For differential addition P+Q (given u(P-Q)):
- U_{P+Q} = 4·(U_P·U_Q - W_P·W_Q)²
- W_{P+Q} = u(P-Q)·4·(U_P·W_Q - U_Q·W_P)²

The implementation uses temporary variables t0-t18 to compute these formulas
efficiently with shared subexpressions.
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
Natural language description:

This function performs the core step of the Montgomery ladder: differential add-and-double.

Given:
- P: A projective point (U_P : W_P) on the Montgomery curve
- Q: A projective point (U_Q : W_Q) on the Montgomery curve
- affine_PmQ: The affine u-coordinate of P-Q  ← **This is the "differential"!**

The function computes:
1. P' = [2]P (the doubling of P)
2. Q' = P+Q (the sum of P and Q, using the differential P-Q)

And returns (P', Q').

**Why we need affine_PmQ (the differential):**
- Standard addition: P + Q needs only P and Q
- Differential addition: P + Q needs P, Q, and P-Q (the difference/differential)
- The differential formula is more efficient for Montgomery curves
- Only the u-coordinate of P-Q is needed, not both coordinates

**Mathematical Interpretation:**

In projective coordinates, a point (U:W) represents the affine u-coordinate u = U/W.
The function relates to the affine point operations defined in `Curve25519Dalek.Math.Montgomery.Curve`:
- If P represents affine point with u-coordinate u_P = U_P/W_P
- If Q represents affine point with u-coordinate u_Q = U_Q/W_Q
- Then P' represents [2]P with u-coordinate U_{P'}/W_{P'}
- And Q' represents P+Q with u-coordinate U_{Q'}/W_{Q'}

The outputs satisfy the mathematical identities from `Montgomery.uADD` and `Montgomery.uDBL`:
- For doubling: The identity relates u([2]P) to u(P) via the curve equation
- For addition: The differential addition formula relates u(P+Q) to u(P), u(Q), and u(P-Q)

Natural language specs:

- The function always succeeds (no panic) given valid field element inputs
- Returns a pair of ProjectivePoints representing ([2]P, P+Q)
- Implements the formulas from Costello-Smith 2017, Algorithm 8
- The computation is constant-time: all operations are field operations
  without branches depending on secret data
- Maintains the Montgomery ladder invariant: if Q = P + diff before the call,
  then after the call, Q' = P' + diff where diff is the point with u-coordinate
  affine_PmQ (the differential!)
-/

-- /-- Convert a projective coordinate pair to the affine u-coordinate u = U/W in the field.
--     Returns 0 if W = 0 (representing the point at infinity). -/
-- noncomputable def projective_to_affine_u (U W : backend.serial.u64.field.FieldElement51) : Montgomery.CurveField :=
--   let u_val : Montgomery.CurveField := Field51_as_Nat U
--   let w_val : Montgomery.CurveField := Field51_as_Nat W
--   if w_val = 0 then 0 else u_val / w_val

/-- **Spec and proof concerning `montgomery.differential_add_and_double`**:

This theorem states that the differential add-and-double operation correctly computes
[2]P and P+Q in projective coordinates, where the results are compatible with the
affine point operations defined in `Curve25519Dalek.Math.Montgomery.Curve`.

**Why "differential"?**
The addition formula is called "differential" because it computes P+Q using the
*difference* P-Q as auxiliary input. Specifically:
- Input: P, Q, and u(P-Q) where u(P-Q) is the u-coordinate of the difference P-Q
- Output: [2]P and P+Q
- The parameter `affine_PmQ` is the "differential" — it provides u(P-Q)

This is different from standard elliptic curve addition, which only needs P and Q.
The differential formula is more efficient for Montgomery curves and is the foundation
of the Montgomery ladder scalar multiplication algorithm.

**Key Properties:**
1. No panic (always returns successfully)
2. Returns two ProjectivePoints (P', Q') representing [2]P and P+Q
3. When converted to affine coordinates, the outputs satisfy the curve point addition
   and doubling laws given by `Montgomery.uADD` and `Montgomery.uDBL`
4. The computation follows Costello-Smith 2017 differential formulas
5. All operations are constant-time field operations

**Mathematical Correctness:**
- The projective coordinates (U:W) represent the affine u-coordinate u = U/W
- For valid inputs with non-zero W coordinates:
  * P'.U/P'.W equals the u-coordinate of [2]P on the Montgomery curve
  * Q'.U/Q'.W equals the u-coordinate of P+Q on the Montgomery curve
  * affine_PmQ represents the u-coordinate of P-Q (the "differential"!)
- The outputs satisfy the identities from `Montgomery.uDBL` for doubling
  and can be used to construct the relation from `Montgomery.uADD` for addition
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
