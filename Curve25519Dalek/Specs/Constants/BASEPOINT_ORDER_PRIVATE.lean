/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-!
# Spec theorem for `curve25519_dalek::constants::BASEPOINT_ORDER_PRIVATE`

This constant represents the order of the Ed25519 basepoint and the Ristretto group,
$$
\ell = 2^{252} + 27742317777372353535851937790883648493.
$$

It is stored as a `Scalar` whose `bytes` field is the canonical 32-byte little-endian
encoding of $\ell$. The constant is used internally to check whether an `EdwardsPoint` is
torsion-free (by multiplying the point by `BASEPOINT_ORDER_PRIVATE` and checking for
identity).

Source: "curve25519-dalek/src/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.constants

/-- **Spec theorem for `curve25519_dalek::constants::BASEPOINT_ORDER_PRIVATE`**
    • The byte representation of BASEPOINT_ORDER_PRIVATE, interpreted as a little-endian
      natural number via U8x32_as_Nat, equals the group order L.
    • The byte representation is canonical, i.e., U8x32_as_Nat(bytes) < 2^256
      (which follows from the previous property since L < 2^256).
-/
@[simp]
theorem BASEPOINT_ORDER_PRIVATE_spec :
    U8x32_as_Nat BASEPOINT_ORDER_PRIVATE.bytes = L := by
  unfold BASEPOINT_ORDER_PRIVATE
  decide

end curve25519_dalek.constants
