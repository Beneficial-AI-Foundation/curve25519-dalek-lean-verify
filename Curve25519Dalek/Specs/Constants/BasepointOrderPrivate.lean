/-
Copyright 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-!
# Spec theorem for `constants::BASEPOINT_ORDER_PRIVATE`

Specification and proof for the constant `BASEPOINT_ORDER_PRIVATE`.

This constant represents the order of the Ed25519 basepoint and the Ristretto group,
$$
\ell = 2^{252} + 27742317777372353535851937790883648493.
$$

It is stored as a 32-byte little-endian encoding inside a `Scalar` struct.

Source: "curve25519-dalek/src/constants.rs"
-/

open Aeneas Aeneas.Std Result
namespace curve25519_dalek.constants

/-
natural language description:

    • constants.BASEPOINT_ORDER_PRIVATE is the order of the Ed25519 basepoint and the
      Ristretto group, i.e., L = 2^252 + 27742317777372353535851937790883648493.
    • It is stored as a `Scalar` whose `bytes` field is the canonical 32-byte little-endian
      encoding of L.
    • This constant is used internally to check whether an EdwardsPoint is torsion-free
      (by multiplying the point by BASEPOINT_ORDER_PRIVATE and checking for identity).

natural language specs:

    • The byte representation of BASEPOINT_ORDER_PRIVATE, interpreted as a little-endian
      natural number via U8x32_as_Nat, equals the group order L.
    • The byte representation is canonical, i.e., U8x32_as_Nat(bytes) < 2^256
      (which follows from the previous property since L < 2^256).
-/

/-- **Spec and proof concerning `constants.BASEPOINT_ORDER_PRIVATE`**:
    • The byte representation of BASEPOINT_ORDER_PRIVATE, interpreted as a little-endian
      natural number via U8x32_as_Nat, equals the group order L.
-/
@[simp]
theorem BASEPOINT_ORDER_PRIVATE_spec :
    U8x32_as_Nat BASEPOINT_ORDER_PRIVATE.bytes = L := by
  unfold BASEPOINT_ORDER_PRIVATE
  decide

end curve25519_dalek.constants
