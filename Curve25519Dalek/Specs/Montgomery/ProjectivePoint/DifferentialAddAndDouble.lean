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

## Mathematical Background

The Montgomery curve for Curve25519 has equation: B·v² = u³ + A·u² + u

In projective coordinates (U:W), a point has affine coordinate u = U/W.
The identity element is represented as (1:0).

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

**Where the "differential" appears in the code:**
- Input parameter: `affine_PmQ : FieldElement51` — This is u(P-Q), the differential!
- In the algorithm (line 105): `t17 = affine_PmQ·t12` — The differential is used here
- In the formula: W_{P+Q} = u(P-Q)·4·(U_P·W_Q - U_Q·W_P)²

**Why is this called "differential"?**
- Because we use the **difference** (P-Q) to help compute the **sum** (P+Q)
- The term "differential" emphasizes that we're working with differences between points
- This is contrast to standard addition formulas that don't require difference information

**Why is this useful?**
The Montgomery ladder algorithm maintains the invariant that two points always differ by
a known amount (the base point). This makes differential addition perfect for efficient,
constant-time scalar multiplication, which is essential for cryptography.

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

/-! ## Helper definitions for connecting projective and affine representations -/

/-- A projective point is valid if its W coordinate is non-zero,
    meaning it represents a finite affine point u = U/W. -/
def ProjectivePoint.IsValid (P : montgomery.ProjectivePoint) : Prop :=
  (Field51_as_Nat P.W : Montgomery.CurveField) ≠ 0

/-! ### Why we can't write `P' = [2]P` directly

**Q: Why not just write `P' = 2 • P` or `P' = [2]P`?**

**A: Because of type mismatch!**

```lean
P  : montgomery.ProjectivePoint  -- Rust FFI structure (U, W fields)
P' : montgomery.ProjectivePoint  -- Rust FFI structure (U, W fields)

[2]P : Montgomery.Point          -- Mathematical affine point (group element)
```

**Key differences:**

1. **`montgomery.ProjectivePoint` has no group structure**
   - It's just a structure with two `FieldElement51` fields
   - No addition `+` or scalar multiplication `•` is defined
   - You cannot write `2 * P` - Lean would error with "failed to synthesize instance HMul"

2. **`Montgomery.Point` is a group element**
   - It's an affine point on the Weierstrass curve (with u and v coordinates)
   - Inherits AddCommGroup instance from mathlib
   - Supports `P + Q` and `n • P` operations

3. **Projective coordinates are equivalence classes**
   - `(U:W) = (λU:λW)` for any λ ≠ 0
   - Many projective representations map to the same affine point
   - E.g., `(4:2)`, `(2:1)`, `(6:3)` all represent affine u-coordinate u = 2

4. **Conversion requires division**
   - Affine: u = U/W (requires field division, non-computable)
   - Projective: (U:W) (no division needed, efficient for computation)

**Our approach: Describe the relationship via coordinate formulas**

Instead of writing `P' = [2]P`, we describe how the projective coordinates of P'
relate to those of P through the doubling formula. This:
- Avoids type conversion overhead
- Directly specifies the implementation behavior
- Makes verification more tractable

The connection to `[2]P` is established in the mathematical interpretation:
"When converted to affine coordinates u' = U'/W' and u = U/W,
 the point with u-coordinate u' equals [2] of the point with u-coordinate u."
-/

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

**Algorithm:**

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
15. t14 = t4·t5 = (U_P + W_P)²(U_P - W_P)²
16. t15 = t13 + t5 = (U_P - W_P)² + ((A+2)/4)·4·U_P·W_P
17. t16 = t6·t15 = 4·U_P·W_P·((U_P - W_P)² + ((A+2)/4)·4·U_P·W_P)
18. t17 = affine_PmQ·t12 = u(P-Q)·4(W_P·U_Q - U_P·W_Q)²  ← **DIFFERENTIAL USED HERE!**
19. t18 = t11 = 4(U_P·U_Q - W_P·W_Q)²

Returns:
- P' with U_{P'} = t14, W_{P'} = t16 (representing [2]P)
- Q' with U_{Q'} = t18, W_{Q'} = t17 (representing P+Q, computed using the differential!)

Note: Only Q' (the addition result) uses the differential affine_PmQ.
      P' (the doubling result) is computed independently without needing the differential.

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

/-! ## Connection to affine curve theorems

This spec relates to the affine point operations defined in `Curve25519Dalek.Math.Montgomery.Curve`:

**Connection to `Montgomery.uDBL`:**
The theorem `Montgomery.uDBL` states that for an affine point P on the Montgomery curve:
```
4 * get_u (2 • P) * get_u (P) * ((get_u P)^2 + A * get_u P + 1) = ((get_u P)^2 - 1)^2
```

When we convert the projective output P' to affine coordinates via u = U/W:
- u([2]P) = P'.U / P'.W should satisfy this identity with u(P) = P.U / P.W

The projective formulas in this spec implement the doubling operation that produces
coordinates satisfying this affine identity.

**Connection to `Montgomery.uADD`:**
The theorem `Montgomery.uADD` states that for affine points P, Q:
```
get_u (P + Q) * get_u (P - Q) * (get_u P - get_u Q)^2 = (get_u P * get_u Q - 1)^2
```

The differential addition formula in this spec computes P+Q given P, Q, and u(P-Q).
When converted to affine coordinates:
- u(P+Q) = Q'.U / Q'.W
- u(P-Q) = affine_PmQ (given as input)
- u(P) = P.U / P.W, u(Q) = Q.U / Q.W

The projective formulas implement the addition that maintains this affine identity.

**Why projective coordinates?**
The projective formulas avoid field divisions (which are expensive) during the computation.
Only when interpreting the result mathematically do we consider the affine form u = U/W.
This makes the Montgomery ladder much more efficient while maintaining mathematical correctness.
-/

/-- Helper: Convert a projective point to its affine representation (if valid).
    This bridges the gap between FFI types and mathematical types. -/
noncomputable def ProjectivePoint.toAffinePoint (proj : montgomery.ProjectivePoint)
    : Option Montgomery.Point :=
  if h : (Field51_as_Nat proj.W : Montgomery.CurveField) ≠ 0 then
    let u := (Field51_as_Nat proj.U : Montgomery.CurveField) /
             (Field51_as_Nat proj.W : Montgomery.CurveField)
    -- Construct affine point from u-coordinate
    -- This requires solving the curve equation, which we defer for now
    sorry
  else none

/-- **High-level mathematical spec**:
    When `differential_add_and_double` succeeds with valid projective points P and Q,
    and affine_PmQ represents the u-coordinate of P-Q, then:
    - P' represents [2]P (doubling)
    - Q' represents P+Q (differential addition)

    This theorem connects the low-level coordinate spec to the high-level
    mathematical operations in `Montgomery.Point`. -/
theorem differential_add_and_double_math_spec
    (P Q : montgomery.ProjectivePoint)
    (affine_PmQ : backend.serial.u64.field.FieldElement51)
    (hP : P.IsValid) (hQ : Q.IsValid) :
    differential_add_and_double P Q affine_PmQ ⦃ res =>
      let (P', Q') := res
      -- When converted to affine points
      ∃ (affP affQ affP' affQ' : Montgomery.Point),
        ProjectivePoint.toAffinePoint P = some affP ∧
        ProjectivePoint.toAffinePoint Q = some affQ ∧
        ProjectivePoint.toAffinePoint P' = some affP' ∧
        ProjectivePoint.toAffinePoint Q' = some affQ' ∧
        -- Mathematical correctness
        affP' = 2 • affP ∧                    -- P' = [2]P
        affQ' = affP + affQ                   -- Q' = P+Q
        -- Note: The differential affine_PmQ ensures the formula works,
        -- but the high-level spec doesn't need to mention it explicitly
    ⦄ := by
  sorry

/-
**Connection theorem** (future work):

The goal is to prove that `differential_add_and_double_spec` (low-level coordinates)
implies `differential_add_and_double_math_spec` (high-level mathematics).

```lean
theorem coordinate_spec_implies_math_spec :
    differential_add_and_double_spec P Q affine_PmQ →
    differential_add_and_double_math_spec P Q affine_PmQ hP hQ
```

This requires:
1. Completing `toAffinePoint` to convert projective to affine
2. Proving that the projective coordinate formulas implement the affine group law
3. Connecting to `Montgomery.uDBL` and `Montgomery.uADD` theorems in Curve.lean

This connection theorem would enable using `differential_add_and_double` in proofs
about high-level operations like scalar multiplication in `Mul.lean`.
-/

end curve25519_dalek.montgomery
