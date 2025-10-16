/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # from_bytes_mod_order_wide

Specification and proof for `Scalar::from_bytes_mod_order_wide`.

This function constructs a scalar from a wide byte array, reducing modulo the group order.

**Source**: curve25519-dalek/src/scalar.rs:L249-L252

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open scalar

/-
natural language description:

    • Converts a [u8;64] array a into a reduced Scalar (mod \ell) named s.
      (The modulus operation is taken within the from_bytes_wide command.)

natural language specs:

    • scalar_to_nat(s) = (u8x64_to_nat(a) mod \ell)
    • scalar_to_nat(s) < \ell
-/
