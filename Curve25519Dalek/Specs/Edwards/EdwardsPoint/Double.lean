/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs

/-! # Spec Theorem for `EdwardsPoint::double`

Specification and proof for `EdwardsPoint::double`.

This function doubles an Edwards point (adds it to itself) using elliptic curve point addition.

**Source**: curve25519-dalek/src/edwards.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Takes an EdwardsPoint and returns the result of adding the point to itself via elliptic curve
point addition (i.e., computes P + P where P is the input point)

• The implementation converts the point to projective coordinates, performs the doubling
operation in projective space, then converts back to extended (= Edwards) coordinates

natural language specs:

• The function always succeeds (no panic)
• Returns an EdwardsPoint that represents P + P (elliptic curve addition) if the input was P
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.double`**:
- No panic (always returns successfully)
- Returns the doubled point 2P (= P + P in elliptic curve addition) where P is the input EdwardsPoint
-/
@[progress]
theorem double_spec (e : EdwardsPoint) :
    ∃ e_double e_plus_e eq_choice,
    double e = ok e_double ∧
    add e e = ok e_plus_e ∧
    ConstantTimeEqcurve25519_dalekedwardsEdwardsPoint.ct_eq e_double e_plus_e = ok eq_choice ∧
    eq_choice = Choice.one := by
    sorry

end curve25519_dalek.edwards.EdwardsPoint
