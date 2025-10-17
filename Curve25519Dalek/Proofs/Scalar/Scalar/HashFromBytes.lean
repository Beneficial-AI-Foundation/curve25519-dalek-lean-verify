/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # hash_from_bytes

Specification and proof for `Scalar::hash_from_bytes`.

This function hashes bytes to produce a scalar.

**Source**: curve25519-dalek/src/scalar.rs:L624-L632

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open scalar

/-
natural language description:

    • Takes as input a variable-length array a of u8 bytes.
      Uses a to subsequently construct a hash function hash.
      Then feeds hash into from_hash to create a canonical Scalar s as
      final output.

natural language specs:

    • The output s is a valid Scalar
    • scalar_to_nat(s) ∈ {0,..., \ell - 1 \}
-/
