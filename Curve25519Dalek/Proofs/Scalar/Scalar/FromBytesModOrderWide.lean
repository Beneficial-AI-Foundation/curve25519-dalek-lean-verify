/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # Spec Theorem for `Scalar::from_bytes_mod_order_wide`

Specification and proof for `Scalar::from_bytes_mod_order_wide`.

This function constructs a scalar from a wide byte array, reducing modulo the group order.

**Source**: curve25519-dalek/src/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.scalar.Scalar

/-
natural language description:

    • Converts a [u8;64] array a into a reduced Scalar (mod \ell) named s.
      (The modulus operation is taken within the from_bytes_wide command.)

natural language specs:

    • scalar_to_nat(s) = (u8x64_to_nat(a) mod \ell)
    • scalar_to_nat(s) < \ell
-/

/-- **Spec and proof concerning `scalar.Scalar.from_bytes_mod_order_wide`**:
- No panic (always returns successfully)
- The result scalar s, when converted to nat, equals the input bytes converted to nat modulo L
- The result scalar s is less than L (the group order)
-/
theorem from_bytes_mod_order_wide_spec (b : Array U8 64#usize):
    ∃ s,
    from_bytes_mod_order_wide b = ok s ∧
    U8x32_as_Nat s.bytes ≡ U8x64_as_Nat b [MOD L] ∧
    U8x32_as_Nat s.bytes < L
    := by
  sorry

end curve25519_dalek.scalar.Scalar
