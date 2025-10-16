/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # invert

Specification and proof for `Scalar::invert`.

This function computes the multiplicative inverse.

**Source**: curve25519-dalek/src/scalar.rs:L746-L749

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open scalar

/-
natural language description:

    • Takes an input Scalar s and returns another Scalar s’ that
      represents the multiplicative inverse of s within the underlying
      field \mathbb{Z} / \ell \mathbb{Z}.

natural language specs:

    • \forall Scalars s:
      scalar_to_nat(s) * scalar_to_nat(s’) is congruent to 1 (mod \ell)
-/
