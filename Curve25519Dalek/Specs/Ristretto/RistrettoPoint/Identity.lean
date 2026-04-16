/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Identity

/-!
# Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::identity`

Returns the identity element of the Ristretto group by delegating to
`EdwardsPoint::identity`, which produces the point with coordinates
(X=0, Y=1, Z=1, T=0).

Source: "curve25519-dalek/src/ristretto.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.ristretto.RistrettoPoint.Insts.Curve25519_dalekTraitsIdentity

/-- **Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::identity`**
• No panic (always returns successfully)
• The resulting RistrettoPoint is the identity element with coordinates
  (X=ZERO, Y=ONE, Z=ONE, T=ZERO)
-/
@[step]
theorem identity_spec :
    identity ⦃ (result : RistrettoPoint) =>
      Field51_as_Nat result.X = 0 ∧
      Field51_as_Nat result.Y = 1 ∧
      Field51_as_Nat result.Z = 1 ∧
      Field51_as_Nat result.T = 0 ⦄ := by
  unfold identity
  step
  tauto

end curve25519_dalek.ristretto.RistrettoPoint.Insts.Curve25519_dalekTraitsIdentity
