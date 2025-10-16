/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # to_bytes

Specification and proof for `Scalar::to_bytes`.

This function converts the structure to a byte array.

**Source**: curve25519-dalek/src/scalar.rs:L690-L693

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open scalar

/-
natural language description:

    • Takes an input Scalar s and returns its constituting
      array a of type [u8;32].

natural language specs:

    • scalar_to_nat(s) = u8x32_to_nat(a)
    • Scalar{a} = s
-/
