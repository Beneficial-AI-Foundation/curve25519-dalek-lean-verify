/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant (Claude Sonnet 4.5)
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

## Mathematical Background

The Montgomery curve for Curve25519 has equation: B·v² = u³ + A·u² + u

In projective coordinates (U:W), a point has affine coordinate u = U/W.
The identity element is represented as (1:0).

The differential addition formulas allow computing P+Q when P-Q is known,
without requiring the full coordinates of P-Q (only its u-coordinate suffices).
This is more efficient and maintains constant-time properties.

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

/-
Natural language description:

This function performs the core step of the Montgomery ladder: differential add-and-double.

Given:
- P: A projective point (U_P : W_P) on the Montgomery curve
- Q: A projective point (U_Q : W_Q) on the Montgomery curve
- affine_PmQ: The affine u-coordinate of P-Q

The function computes:
1. P' = [2]P (the doubling of P)
2. Q' = P+Q (the sum of P and Q)

And returns (P', Q').

The computation follows Algorithm 8 from Costello-Smith 2017, using the differential
addition formulas that only require knowing the u-coordinate of P-Q rather than both
coordinates. This is crucial for the Montgomery ladder's efficiency and constant-time
properties.

The algorithm computes:
1. t0 = U_P + W_P
2. t1 = U_P - W_P
3. t2 = U_Q + W_Q
4. t3 = U_Q - W_Q
5. t4 = t0² = (U_P + W_P)²
6. t5 = t1² = (U_P - W_P)²
7. t6 = t4 - t5 = 4·U_P·W_P
8. t7 = t0·t3 = (U_P + W_P)(U_Q - W_Q)
9. t8 = t1·t2 = (U_P - W_P)(U_Q + W_Q)
10. t9 = t7 + t8 = 2(U_P·U_Q - W_P·W_Q)
11. t10 = t7 - t8 = 2(W_P·U_Q - U_P·W_Q)
12. t11 = t9² = 4(U_P·U_Q - W_P·W_Q)²
13. t12 = t10² = 4(W_P·U_Q - U_P·W_Q)²
14. t13 = ((A+2)/4)·t6 = ((A+2)/4)·4·U_P·W_P
15. t14 = t4·t5 = (U_P² - W_P²)²
16. t15 = t13 + t5 = (U_P - W_P)² + ((A+2)/4)·4·U_P·W_P
17. t16 = t6·t15 = 4·U_P·W_P·((U_P - W_P)² + ((A+2)/4)·4·U_P·W_P)
18. t17 = affine_PmQ·t12 = u(P-Q)·4(W_P·U_Q - U_P·W_Q)²
19. t18 = t11 = 4(U_P·U_Q - W_P·W_Q)²

Returns:
- P' with U_{P'} = t14, W_{P'} = t16 (representing [2]P)
- Q' with U_{Q'} = t18, W_{Q'} = t17 (representing P+Q)

Natural language specs:

- The function always succeeds (no panic) given valid field element inputs
- Returns a pair of ProjectivePoints representing ([2]P, P+Q)
- Implements the formulas from Costello-Smith 2017, Algorithm 8
- The computation is constant-time: all operations are field operations
  without branches depending on secret data
- Maintains the Montgomery ladder invariant: if Q = P + diff before the call,
  then after the call, Q' = P' + diff where diff is the point with u-coordinate
  affine_PmQ
-/

/-- **Spec and proof concerning `montgomery.differential_add_and_double`**:
- No panic (always returns successfully)
- Returns two ProjectivePoints (P', Q') where:
  * P' represents [2]P (the doubling of P)
  * Q' represents P+Q (the sum of P and Q)
- The computation follows the differential addition and doubling formulas
  from Costello-Smith 2017
- Mathematical properties:
  * If P and Q represent affine points with u-coordinates u_P and u_Q respectively,
    and affine_PmQ represents the u-coordinate of P-Q, then:
    - P'.U/P'.W represents the u-coordinate of [2]P (if W ≠ 0)
    - Q'.U/Q'.W represents the u-coordinate of P+Q (if W ≠ 0)
  * The formulas maintain the Montgomery ladder invariant throughout scalar
    multiplication
  * All operations are constant-time field operations
-/
@[progress]
theorem differential_add_and_double_spec
    (P Q : montgomery.ProjectivePoint)
    (affine_PmQ : backend.serial.u64.field.FieldElement51) :
    differential_add_and_double P Q affine_PmQ ⦃ res =>
      let (P', Q') := res
      -- P' and Q' are valid ProjectivePoints
      -- P' represents [2]P (doubling of P)
      -- Q' represents P+Q (addition of P and Q)
      -- The computation maintains the Montgomery ladder invariant:
      -- If initially Q - P has u-coordinate affine_PmQ,
      -- then Q' - P' also has u-coordinate affine_PmQ
      True -- Placeholder for full mathematical specification
    ⦄ := by
  sorry

end curve25519_dalek.montgomery
