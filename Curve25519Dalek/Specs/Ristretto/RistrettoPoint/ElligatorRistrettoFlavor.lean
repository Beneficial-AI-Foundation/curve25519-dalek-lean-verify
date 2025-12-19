/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Defs.Edwards.Representation

/-! # Spec Theorem for `RistrettoPoint::elligator_ristretto_flavor`

Specification and proof for `RistrettoPoint::elligator_ristretto_flavor`.

This function implements the Ristretto Elligator map, which is the MAP function
defined in the

- [Ristretto specification](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#section-4.3.4).

It maps an arbitrary field element to a valid Ristretto point (which represents an equivalence
class of 8 Edwards points).

**Source**: curve25519-dalek/src/ristretto.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.curve_models (ProjectivePoint)
namespace curve25519_dalek.ristretto.RistrettoPoint

/-
natural language description:

• Takes a field element r₀ and maps it to a valid RistrettoPoint (which represents an equivalence class
  of 8 Edwards points) using the Elligator map:
  https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#section-4.3.4
  Arithmetics are performed in the field 𝔽ₚ where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic) for all field element inputs
• Given an input field element r₀, the output RistrettoPoint indeed lies on the Curve25519 Edwards curve, i.e.,
  it indeed fulfils the curve equation.
-/

/-- **Spec and proof concerning `ristretto.RistrettoPoint.elligator_ristretto_flavor`**:
• The function always succeeds (no panic) for all field element inputs
• Given an input field element r₀, the output RistrettoPoint indeed lies on the Curve25519 Edwards curve, i.e.,
  it indeed fulfils the curve equation.
-/
theorem elligator_ristretto_flavor_spec
  (r_0 : backend.serial.u64.field.FieldElement51)
  (h_r_0_bounds : ∀ i, i < 5 → (r_0[i]!).val < 2 ^ 54) :
  ∃ rist,
    elligator_ristretto_flavor r_0 = ok rist ∧
    rist.IsValid := by
  sorry

end curve25519_dalek.ristretto.RistrettoPoint
