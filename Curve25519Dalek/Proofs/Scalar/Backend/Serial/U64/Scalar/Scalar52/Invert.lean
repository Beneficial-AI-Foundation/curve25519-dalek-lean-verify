/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # invert

Specification and proof for `Scalar52::invert`.

This function computes the multiplicative inverse.

**Source**: curve25519-dalek/src/scalar.rs:L1205-L1208

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek

/-
natural language description:

    • Takes as input an UnpackedScalar r and returns another UnpackedScalar r’ that
      represents the multiplicative inverse of r within the underlying
      field \mathbb{Z} / \ell \mathbb{Z}. This is done by first
      converting r into Montgomery form, then inverting with
      montgomery_invert, and then converting back into UnpackedScalar.

natural language specs:

    • \forall UnpackedScalars r with r ≠ 0:
      scalar_to_nat(r) * scalar_to_nat(r’) is congruent to 1 (mod \ell)
-/
