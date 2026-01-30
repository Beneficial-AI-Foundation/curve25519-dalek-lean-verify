/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs.Edwards.Representation

/-! # Spec Theorem for `RistrettoPoint::elligator_ristretto_flavor`

Specification and proof for `RistrettoPoint::elligator_ristretto_flavor`.

This function implements the Ristretto Elligator map, which is the MAP function
defined in the

- [Ristretto specification](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#section-4.3.4).

It maps an arbitrary field element s to a valid Ristretto point.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.ristretto.RistrettoPoint

/-
natural language description:

• Takes a field element s and maps it to a valid RistrettoPoint using the Elligator map:

  https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#section-4.3.4

  Arithmetics are performed in the field 𝔽ₚ where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic) for all valid field element inputs s
• The output is indeed a valid RistrettoPoint (i.e., an even Edwards point that lies on the curve)
-/

/-- **Spec and proof concerning `ristretto.RistrettoPoint.elligator_ristretto_flavor`**:
• The function always succeeds (no panic) for all valid field element inputs
• The output is indeed a valid RistrettoPoint (i.e., an even Edwards point that lies on the curve)
-/
theorem elligator_ristretto_flavor_spec
    (s : backend.serial.u64.field.FieldElement51)
    (h_s_valid : s.IsValid) :

  ∃ rist, elligator_ristretto_flavor s = ok rist ∧

  -- Note that validity here also implicitly guarantees the (correct but not immediately obvious) property that the elligator map only generates even Edwards points
  rist.IsValid

  := by

  sorry

  /-
  Note: An optional, potentially desirable extension of this spec theorem may be to
  define a purely mathematical version f_ell of the elligator map in Representation.lean
  that maps mathematical field elements to even Edwards points and then subsequently
  show that f_ell(s.toField) = rist.toPoint.
  -/

end curve25519_dalek.ristretto.RistrettoPoint
