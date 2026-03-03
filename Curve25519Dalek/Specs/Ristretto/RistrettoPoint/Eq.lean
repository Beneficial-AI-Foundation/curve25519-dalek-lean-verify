/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Ristretto.RistrettoPoint.CtEq

/-! # Spec Theorem for `RistrettoPoint::eq`

Specification and proof for the `PartialEq` trait implementation for `RistrettoPoint`.

This function checks equality of two Ristretto points by delegating to constant-time
equality comparison via `ct_eq` and converting the resulting `Choice` to a `Bool`.

**Source**: curve25519-dalek/src/ristretto.rs, lines 859:4-861:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51

namespace curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreCmpPartialEqRistrettoPoint

/-
natural language description:

    Compares two RistrettoPoint values for equality by delegating to the constant-time
    equality check `ct_eq` and converting the resulting `Choice` to a `Bool`.

    The implementation:
      1. Calls `RistrettoPoint.ct_eq(self, other)` to get a `Choice`
      2. Converts the `Choice` to `Bool` via `From<Choice> for bool`
         (Choice.one → true, Choice.zero → false)

natural language specs:

    Requires: X and Y coordinate limbs of both points are bounded by ≤ 2^53
    (inherited from ct_eq preconditions for field multiplication).

    Postcondition: The result is true if and only if
      Field51_as_Nat(self.X) * Field51_as_Nat(other.Y) ≡ Field51_as_Nat(self.Y) * Field51_as_Nat(other.X) (mod p)
    OR
      Field51_as_Nat(self.X) * Field51_as_Nat(other.X) ≡ Field51_as_Nat(self.Y) * Field51_as_Nat(other.Y) (mod p)
-/

/-- **Spec and proof concerning `ristretto.RistrettoPoint.Insts.CoreCmpPartialEqRistrettoPoint.eq`**:
- No panic (always returns successfully given bounded inputs)
- Returns true iff the two points satisfy the Ristretto equivalence condition:
  X1·Y2 ≡ Y1·X2 (mod p) or X1·X2 ≡ Y1·Y2 (mod p)
- Implemented via constant-time equality followed by Choice-to-Bool conversion
-/
@[progress]
theorem eq_spec (self other : ristretto.RistrettoPoint)
  (h_self_X : ∀ i, i < 5 → self.X.val[i]!.val ≤ 2 ^ 53)
  (h_self_Y : ∀ i, i < 5 → self.Y.val[i]!.val ≤ 2 ^ 53)
  (h_other_X : ∀ i, i < 5 → other.X.val[i]!.val ≤ 2 ^ 53)
  (h_other_Y : ∀ i, i < 5 → other.Y.val[i]!.val ≤ 2 ^ 53) :
  eq self other ⦃ b =>
  (b = true ↔
    (Field51_as_Nat self.X * Field51_as_Nat other.Y) ≡ (Field51_as_Nat self.Y * Field51_as_Nat other.X) [MOD p] ∨
    (Field51_as_Nat self.X * Field51_as_Nat other.X) ≡ (Field51_as_Nat self.Y * Field51_as_Nat other.Y) [MOD p]) ⦄ := by
  sorry

end curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreCmpPartialEqRistrettoPoint
