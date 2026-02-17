/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.CtEq
/-! # Spec Theorem for `MontgomeryPoint::eq`

Specification and proof for
`curve25519_dalek::montgomery::{core::cmp::PartialEq<curve25519_dalek::montgomery::MontgomeryPoint> for curve25519_dalek::montgomery::MontgomeryPoint}::eq`.

This function compares two MontgomeryPoint values by checking constant-time
field element equality of their u-coordinates, then converting the resulting
Choice into a Bool.

**Source**: curve25519-dalek/src/montgomery.rs, lines 94:4-96:5

-/

open Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint

/-
natural language description:

• Compares two MontgomeryPoint values by constant-time equality of their
  u-coordinates (decoded as FieldElement51).

• The result Choice is converted into Bool via FromBoolChoice.

natural language specs:

• The function always succeeds (no panic)
• The result is true iff the underlying field elements represent the same
  value modulo p
-/

/-- **Spec and proof concerning `montgomery.PartialEqMontgomeryPointMontgomeryPoint.eq`**:
- No panic (always returns successfully)
- Returns true iff the u-coordinates are equal modulo p
- Implemented via constant-time equality followed by Choice-to-Bool conversion
-/
/- OLD PROOF
@[progress]
theorem eq_spec (u v : MontgomeryPoint) :
    ∃ b,
    eq u v = ok b ∧
    (b = true ↔
      (U8x32_as_Nat u % 2 ^ 255) ≡ (U8x32_as_Nat v % 2 ^ 255) [MOD p]) := by
    unfold eq
    progress*
    unfold subtle.FromBoolChoice.from
    progress*
    simp_all
    rw[← c_post]
    cases c with
    | mk val valid =>
      simp [Choice.one]
-/

@[progress]
theorem eq_spec (u v : MontgomeryPoint) :
    spec (eq u v) (fun b =>
    (b = true ↔
      (U8x32_as_Nat u % 2 ^ 255) ≡ (U8x32_as_Nat v % 2 ^ 255) [MOD p])) := by
    unfold eq
    sorry

end curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint
