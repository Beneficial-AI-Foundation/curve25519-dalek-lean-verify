/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # montgomery_invert

Specification and proof for `Scalar52::montgomery_invert`.

This function computes the multiplicative inverse using Montgomery form.

**Source**: curve25519-dalek/src/scalar.rs:L1149-L1203

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek

/-
natural language description:

    • Takes as input an UnpackedScalar r that is assumed to be
      in Montgomery form. Then efficiently computes and returns an
      UnpackedScalar r' (also in Montgomery form)  that represents
      the multiplicative inverse of r within the underlying field
      \mathbb{Z} / \ell \mathbb{Z}.

natural language specs:

    • \forall UnpackedScalars r in Montgomery form with r ≠ 0:
      scalar_to_nat(r) * scalar_to_nat(r’) is congruent to 1 (mod \ell)
-/
