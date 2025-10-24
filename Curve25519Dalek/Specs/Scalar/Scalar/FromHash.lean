/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # from_hash

Specification and proof for `Scalar::from_hash`.

This function constructs a scalar from a hash output.

**Source**: curve25519-dalek/src/scalar.rs:L670-L678

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open scalar

/-
natural language description:

    • Takes as input a hash function "hash" that generates
      64 bytes (512 bit) as output. Uses the hash function
      to generate a hash code to then fill in an array a of type
      [u8;64]. This array is then converted to a canonical
      Scalar s via from_bytes_mod_order_wide(a).

natural language specs:

    • The output s is a valid Scalar
    • scalar_to_nat(s) ∈ {0,..., \ell - 1 \}
-/
