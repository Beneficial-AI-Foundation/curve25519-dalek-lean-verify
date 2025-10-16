/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # from_bytes_mod_order

Specification and proof for `Scalar::from_bytes_mod_order`.

This function constructs a scalar from bytes, reducing modulo the group order.

**Source**: curve25519-dalek/src/scalar.rs:L236-L246

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open scalar

/-
natural language description:

    • Converts a [u8;32] array a into a Scalar, then takes the modulus
      with respect to the group order \ell, and then returns the
      reduced Scalar (mod \ell) which we name s.

natural language specs:

    • scalar_to_nat(s) = (u8x32_to_nat(a) mod \ell)
    • scalar_to_nat(s) < \ell
-/
