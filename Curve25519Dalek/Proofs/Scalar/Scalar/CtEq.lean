/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # ct_eq

Specification and proof for `scalar::Scalar::ct_eq`.

This function performs constant-time equality comparison.

**Source**: curve25519-dalek/src/scalar.rs:L300-L304

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open scalar

/-
natural language description:

    • Compares two scalar types to determine whether they are equal or not.

    • Crucially does so in constant time irrespective of the inputs as to avoid security liabilities.

natural language specs:

    • scalar_to_nat(self) = scalar_to_nat(other) \iff Choice = True
-/
